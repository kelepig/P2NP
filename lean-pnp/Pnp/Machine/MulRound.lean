/-
  文件：Pnp/Machine/MulRound.lean
  File: Pnp/Machine/MulRound.lean

  主题：**unary 乘法的一轮：复制遍 → 消费一个 B 格 → 恢复 A**。
  Topic: one round of the unary multiplication machine: copy pass, consume one `B` cell,
  restore `A`.

  三个相位机（`mulCopy` / `mulConsume` / `mulRestore`）各自以接受态收尾。用 `seqComp` 串联
  时必须提供「相位在收尾前不停机」——这正是各相位机逐段走位所保证的；本文件先机检这些
  不停机事实，再给出整轮机器与整轮运行定理。
  Each phase machine halts exactly at its terminal state. To chain them with `seqComp` we must
  know that no phase halts before its end; this file proves those facts and then the round.

  通用工具（与具体机器无关）：
    - `no_halt_of_state_eq`：若运行途中的状态恒为某个非终止态，则这段不停机；
    - `no_halt_add`：两段各自不停机 ⇒ 拼接后整段不停机。
-/

import Pnp.Machine.MulRestore
import Pnp.Machine.SeqComp

namespace Pnp

namespace DTM

/-! ### 三段走位「状态不变」引理 -/

/-- 状态 5 向左走过 `m` 个标记源格（含最后落定的一步）时，状态恒为 5。
    State 5 stays put while walking left over `m` marked source cells (final step included). -/
theorem mulCopy_skip5_state : ∀ (m : Nat) (P R : List Sym) (j : Nat), j ≤ m + 1 →
    (mulCopy.run j ⟨(⟨5, by omega⟩ : Fin 8),
        Tape.mk (List.replicate m (some false) ++ none :: P) (some false :: R)⟩).state
      = (⟨5, by omega⟩ : Fin 8)
  | 0, P, R, j, hj => by
      rcases j with _ | j'
      · rfl
      · have hj1 : j' = 0 := by omega
        subst hj1
        rw [estepMC 5 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  | m + 1, P, R, j, hj => by
      rcases j with _ | j'
      · rfl
      · rw [show j' + 1 = 1 + j' from by omega, DTM.run_add mulCopy 1 j']
        rw [estepMC 5 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
        etape
        exact mulCopy_skip5_state m P (some false :: R) j' (by omega)

/-- 状态 4 向右走过 `m` 个 `some false` 副本格时，状态恒为 4。
    State 4 stays put while walking right over `m` copy cells. -/
theorem mulConsume_skipA_state : ∀ (m : Nat) (P R : List Sym) (j : Nat), j ≤ m →
    (mulConsume.run j ⟨(⟨4, by omega⟩ : Fin 6),
        Tape.mk P (List.replicate m (some false) ++ (none :: R))⟩).state
      = (⟨4, by omega⟩ : Fin 6)
  | 0, P, R, j, hj => by
      have hj0 : j = 0 := by omega
      subst hj0
      rfl
  | m + 1, P, R, j, hj => by
      rcases j with _ | j'
      · rfl
      · rw [List.replicate_succ, List.cons_append]
        rw [show j' + 1 = 1 + j' from by omega, DTM.run_add mulConsume 1 j']
        rw [estepMCn 4 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
        etape
        exact mulConsume_skipA_state m (some false :: P) R j' (by omega)

/-- 状态 2 向右走过 `m'` 个 `some true` 恢复格的走位段（含最后落定的一步），状态恒为 2。
    State 2 stays put while walking right over `m'` restored cells (final step included). -/
theorem mulRestore_skipT_state : ∀ (m m' : Nat) (P Q : List Sym) (j : Nat), j ≤ m' + 1 →
    (mulRestore.run j ⟨(⟨2, by omega⟩ : Fin 4),
        Tape.mk (List.replicate m (some true) ++ (none :: P))
          (some true :: (List.replicate m' (some true) ++ (none :: Q)))⟩).state
      = (⟨2, by omega⟩ : Fin 4)
  | m, 0, P, Q, j, hj => by
      rcases j with _ | j'
      · rfl
      · have hj1 : j' = 0 := by omega
        subst hj1
        rw [estepMR 2 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  | m, m' + 1, P, Q, j, hj => by
      rcases j with _ | j'
      · rfl
      · rw [List.replicate_succ, List.cons_append]
        rw [show j' + 1 = 1 + j' from by omega, DTM.run_add mulRestore 1 j']
        rw [estepMR 2 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
        etape
        exact mulRestore_skipT_state (m + 1) m' P Q j' (by omega)

/-! ### 三段收尾走位的不停机 -/

/-- 复制遍收尾走位（状态 5 走到 `sepB`）在最后一步之前不停机。 -/
theorem mulCopy_skip5_no_halt (m : Nat) (P R : List Sym) :
    ∀ k, k < m + 2 →
      mulCopy.halted (mulCopy.run k ⟨(⟨5, by omega⟩ : Fin 8),
        Tape.mk (List.replicate m (some false) ++ none :: P) (some false :: R)⟩) = false :=
  no_halt_of_state_eq mulCopy (m + 2) _ (⟨5, by omega⟩ : Fin 8)
    (by decide) (by decide) (fun k hk => mulCopy_skip5_state m P R k (by omega))

/-- 消费遍收尾走位（状态 4 穿过 A）在最后一步之前不停机。 -/
theorem mulConsume_skipA_no_halt (m : Nat) (P R : List Sym) :
    ∀ k, k < m + 1 →
      mulConsume.halted (mulConsume.run k ⟨(⟨4, by omega⟩ : Fin 6),
        Tape.mk P (List.replicate m (some false) ++ (none :: R))⟩) = false :=
  no_halt_of_state_eq mulConsume (m + 1) _ (⟨4, by omega⟩ : Fin 6)
    (by decide) (by decide) (fun k hk => mulConsume_skipA_state m P R k (by omega))

/-- 恢复遍收尾走位（状态 2 回到 A 最右格）在最后一步之前不停机。 -/
theorem mulRestore_skipT_no_halt (m m' : Nat) (P Q : List Sym) :
    ∀ k, k < m' + 2 →
      mulRestore.halted (mulRestore.run k ⟨(⟨2, by omega⟩ : Fin 4),
        Tape.mk (List.replicate m (some true) ++ (none :: P))
          (some true :: (List.replicate m' (some true) ++ (none :: Q)))⟩) = false :=
  no_halt_of_state_eq mulRestore (m' + 2) _ (⟨2, by omega⟩ : Fin 4)
    (by decide) (by decide) (fun k hk => mulRestore_skipT_state m m' P Q k (by omega))

/-- `⟨s, _⟩` 与 `mulCopy` 接受态不同（`s ≠ 6`）。 -/
theorem mulCopy_ne_accept {s : Nat} (hs : s < 8) (h : s ≠ 6) :
    (⟨s, hs⟩ : Fin 8) ≠ mulCopy.accept := by
  intro he
  have hv : s = 6 := by
    have := congrArg Fin.val he
    rwa [show mulCopy.accept.val = 6 from rfl] at this
  exact h hv

/-- `⟨s, _⟩` 与 `mulCopy` 拒绝态不同（`s ≠ 6`）。 -/
theorem mulCopy_ne_reject {s : Nat} (hs : s < 8) (h : s ≠ 6) :
    (⟨s, hs⟩ : Fin 8) ≠ mulCopy.reject := by
  intro he
  have hv : s = 6 := by
    have := congrArg Fin.val he
    rwa [show mulCopy.reject.val = 6 from rfl] at this
  exact h hv

/-! ### 三个相位的全程不停机 -/

/-- **消费遍全程不停机**：`a + 2u + 4` 步内从不接受（唯一终止在最后一步）。
    The consume phase never halts before its final step. -/
theorem mulConsume_no_halt (a u r : Nat) (h : 1 ≤ u) (L M : List Sym) :
    ∀ k, k < a + 2 * u + 4 →
      mulConsume.halted (mulConsume.run k ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate u (some true) ++
            (List.replicate r (some false) ++ (none :: (none :: L))))
          (none :: (List.replicate a (some false) ++ (none :: M)))⟩) = false := by
  rcases u with _ | u'
  · omega
  simp only [List.replicate_succ, List.cons_append, Nat.add_sub_cancel]
  rw [show a + 2 * (u' + 1) + 4 = 1 + ((u' + 3) + ((u' + 1) + (a + 1))) from by omega]
  refine no_halt_add mulConsume 1 ((u' + 3) + ((u' + 1) + (a + 1))) _ ?_ ?_
  · exact no_halt_one mulConsume _ (mulConsume_halted_ne 0 (by omega) (by omega) _)
  · rw [estepMCn 0 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
    etape
    refine no_halt_add mulConsume (u' + 3) ((u' + 1) + (a + 1)) _ ?_ ?_
    · intro k hk
      refine halted_false_before mulConsume (u' + 3) _ ?_ ?_ k hk
      · rw [mulConsume_toFlip u' r L (none :: (List.replicate a (some false) ++ (none :: M)))]
        simp [mulConsume]
      · rw [mulConsume_toFlip u' r L (none :: (List.replicate a (some false) ++ (none :: M)))]
        simp [mulConsume]
    · rw [mulConsume_toFlip u' r L (none :: (List.replicate a (some false) ++ (none :: M)))]
      refine no_halt_add mulConsume (u' + 1) (a + 1) _ ?_ ?_
      · intro k hk
        refine halted_false_before mulConsume (u' + 1) _ ?_ ?_ k hk
        · rw [mulConsume_skipR u'
            (some false :: (List.replicate r (some false) ++ (none :: (none :: L))))
            (List.replicate a (some false) ++ (none :: M))]
          simp [mulConsume]
        · rw [mulConsume_skipR u'
            (some false :: (List.replicate r (some false) ++ (none :: (none :: L))))
            (List.replicate a (some false) ++ (none :: M))]
          simp [mulConsume]
      · rw [mulConsume_skipR u'
          (some false :: (List.replicate r (some false) ++ (none :: (none :: L))))
          (List.replicate a (some false) ++ (none :: M))]
        exact mulConsume_skipA_no_halt a (none :: (List.replicate u' (some true) ++
          (some false :: (List.replicate r (some false) ++ (none :: (none :: L)))))) M

/-- **恢复遍全程不停机**：`2a + 3` 步内从不接受。
    The restore phase never halts before its final step. -/
theorem mulRestore_no_halt (a : Nat) (h : 1 ≤ a) (P Q : List Sym) :
    ∀ k, k < 2 * a + 3 →
      mulRestore.halted (mulRestore.run k ⟨(⟨0, by omega⟩ : Fin 4),
        Tape.mk (List.replicate a (some false) ++ (none :: P)) (none :: Q)⟩) = false := by
  rcases a with _ | a'
  · omega
  simp only [List.replicate_succ, List.cons_append, Nat.add_sub_cancel]
  rw [show 2 * (a' + 1) + 3 = (a' + 3) + (a' + 2) from by omega]
  refine no_halt_add mulRestore (a' + 3) (a' + 2) _ ?_ ?_
  · intro k hk
    refine halted_false_before mulRestore (a' + 3) _ ?_ ?_ k hk
    · rw [show a' + 3 = 1 + (a' + (1 + 1)) from by omega]
      rw [DTM.run_add mulRestore 1 (a' + (1 + 1)),
        estepMR 0 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [DTM.run_add mulRestore a' (1 + 1),
        mulRestore_flip a' (none :: P) (none :: Q)]
      rw [DTM.run_add mulRestore 1 1,
        estepMR 1 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [estepMR 1 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
      etape
      simp [mulRestore]
    · rw [show a' + 3 = 1 + (a' + (1 + 1)) from by omega]
      rw [DTM.run_add mulRestore 1 (a' + (1 + 1)),
        estepMR 0 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [DTM.run_add mulRestore a' (1 + 1),
        mulRestore_flip a' (none :: P) (none :: Q)]
      rw [DTM.run_add mulRestore 1 1,
        estepMR 1 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [estepMR 1 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
      etape
      simp [mulRestore]
  · rw [show a' + 3 = 1 + (a' + (1 + 1)) from by omega]
    rw [DTM.run_add mulRestore 1 (a' + (1 + 1)),
      estepMR 0 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
    etape
    rw [DTM.run_add mulRestore a' (1 + 1),
      mulRestore_flip a' (none :: P) (none :: Q)]
    rw [DTM.run_add mulRestore 1 1,
      estepMR 1 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
    etape
    rw [estepMR 1 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
    etape
    exact mulRestore_skipT_no_halt 0 a' P Q

/-- 复制遍「唯一一轮」（源块只有一格、副本区为空）的前 4 步停在状态 5。
    The first four steps of the single-cell copy unit end in state 5. -/
theorem mulCopy_last0_cum (b r w : Nat) (hw : 1 ≤ w) (L R : List Sym) :
    mulCopy.run 4
      ⟨(⟨0, by omega⟩ : Fin 8), Tape.mk (mulB b r L) (mulR 0 0 w R)⟩
      = ⟨(⟨5, by omega⟩ : Fin 8),
          Tape.mk (mulB b r L)
            (some false :: none :: some false ::
              (List.replicate w (none : Sym) ++ R))⟩ := by
  simp only [mulR, List.replicate_zero, List.nil_append]
  rw [show (4 : Nat) = 1 + (1 + (1 + 1)) from by omega]
  rw [DTM.run_add mulCopy 1 (1 + (1 + 1)),
    estepMC 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [DTM.run_add mulCopy 1 (1 + 1),
    mulCopy_cross1 (some false :: mulB b r L) none (List.replicate w (none : Sym) ++ R)]
  rw [DTM.run_add mulCopy 1 1,
    mulCopy_write2_none (some false :: mulB b r L) (List.replicate w (none : Sym) ++ R)]
  rw [mulCopy_cross4 (some false) (mulB b r L) (some false) (List.replicate w (none : Sym) ++ R)]

/-- 源块只有一格时的复制遍不停机（6 步，唯一终止在最后一步）。 -/
theorem mulCopy_last0_no_halt (b r w : Nat) (hw : 1 ≤ w) (L R : List Sym) :
    ∀ k, k < 6 →
      mulCopy.halted (mulCopy.run k ⟨(⟨0, by omega⟩ : Fin 8),
        Tape.mk (mulB b r L) (mulR 0 0 w R)⟩) = false := by
  rw [show (6 : Nat) = 4 + 2 from by omega]
  refine no_halt_add mulCopy 4 2 _ ?_ ?_
  · exact no_halt_of_run_end mulCopy 4 _ (⟨5, by omega⟩ : Fin 8) _
      (mulCopy_last0_cum b r w hw L R) (mulCopy_ne_accept (by omega) (by omega))
      (mulCopy_ne_reject (by omega) (by omega))
  · rw [mulCopy_last0_cum b r w hw L R]
    exact mulCopy_skip5_no_halt 0
      (List.replicate (b - r) (some true) ++ List.replicate r (some false) ++ (none :: (none :: L)))
      (none :: (some false :: (List.replicate w (none : Sym) ++ R)))

/-- 复制遍最后一轮的前 `2d + i + 4` 步停在状态 5（源区走完、副本区落定）。
    The copy pass's last round reaches state 5 after `2d + i + 4` steps. -/
theorem mulCopy_last_cum (a b r w d i : Nat) (hi : i + 1 = a) (hd : 1 ≤ d) (L R : List Sym) :
    mulCopy.run (2 * d + i + 4)
      ⟨(⟨0, by omega⟩ : Fin 8), Tape.mk (mulL a b r i L) (mulR d i w R)⟩
      = ⟨(⟨5, by omega⟩ : Fin 8),
          Tape.mk (List.replicate i (some false) ++ mulB b r L)
            (some false :: none :: some false ::
              (List.replicate (d - 1) (some false) ++
                (some false :: (List.replicate w (none : Sym) ++ R))))⟩ := by
  have hd1 : List.replicate d (some false) = some false :: List.replicate (d - 1) (some false) := by
    cases d with
    | zero => omega
    | succ k => rw [List.replicate_succ, show k + 1 - 1 = k from by omega]
  simp only [mulL, mulR]
  rw [show 2 * d + i + 4 = 1 + ((i + 1) + ((d + 1) + ((d - 1) + 1 + 1))) from by omega]
  rw [DTM.run_add mulCopy 1 ((i + 1) + ((d + 1) + ((d - 1) + 1 + 1))),
    estepMC 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [DTM.run_add mulCopy (i + 1) ((d + 1) + ((d - 1) + 1 + 1))]
  rw [DTM.run_add mulCopy i 1]
  rw [mulCopy_skip1 i (some false :: (List.replicate (a - 1 - i) (some true) ++ mulB b r L))
        (none :: (List.replicate d (some false) ++ (none :: (List.replicate w (none : Sym) ++ R))))]
  rw [hd1, List.cons_append]
  rw [mulCopy_cross1 (List.replicate i (some false) ++
        (some false :: (List.replicate (a - 1 - i) (some true) ++ mulB b r L))) (some false)
        (List.replicate (d - 1) (some false) ++ (none :: (List.replicate w (none : Sym) ++ R)))]
  rw [DTM.run_add mulCopy (d + 1) ((d - 1) + 1 + 1)]
  rw [DTM.run_add mulCopy d 1]
  rw [show some false :: (List.replicate (d - 1) (some false) ++
        (none :: (List.replicate w (none : Sym) ++ R)))
      = List.replicate d (some false) ++ (none :: (List.replicate w (none : Sym) ++ R)) from by
    rw [hd1, List.cons_append]]
  rw [mulCopy_skip2 d (none :: (List.replicate i (some false) ++
        (some false :: (List.replicate (a - 1 - i) (some true) ++ mulB b r L))))
        (none :: (List.replicate w (none : Sym) ++ R))]
  rw [show List.replicate d (some false) ++ (none :: (List.replicate i (some false) ++
        (some false :: (List.replicate (a - 1 - i) (some true) ++ mulB b r L))))
      = some false :: (List.replicate (d - 1) (some false) ++ (none ::
        (List.replicate i (some false) ++
          (some false :: (List.replicate (a - 1 - i) (some true) ++ mulB b r L))))) from by
    rw [hd1, List.cons_append]]
  rw [mulCopy_write2_some (List.replicate (d - 1) (some false) ++ (none ::
        (List.replicate i (some false) ++
          (some false :: (List.replicate (a - 1 - i) (some true) ++ mulB b r L)))))
        (List.replicate w (none : Sym) ++ R)]
  rw [DTM.run_add mulCopy ((d - 1) + 1) 1]
  rw [DTM.run_add mulCopy (d - 1) 1]
  rw [mulCopy_skip4 (d - 1) (none :: (List.replicate i (some false) ++
        (some false :: (List.replicate (a - 1 - i) (some true) ++ mulB b r L))))
        (some false :: (List.replicate w (none : Sym) ++ R))]
  rw [show (d - 1) + 1 = d from by omega]
  rw [show List.replicate d (some false) ++ (some false :: (List.replicate w (none : Sym) ++ R))
      = some false :: (List.replicate (d - 1) (some false) ++
          (some false :: (List.replicate w (none : Sym) ++ R))) from by
    rw [hd1, List.cons_append]]
  rw [estepMC 4 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega : (4 : Nat) ≠ 6)]
  etape
  rw [show List.replicate i (some false) ++
        (some false :: (List.replicate (a - 1 - i) (some true) ++ mulB b r L))
      = List.replicate (i + 1) (some false) ++
        (List.replicate (a - 1 - i) (some true) ++ mulB b r L) from
    replicate_succ_append i (some false) (List.replicate (a - 1 - i) (some true) ++ mulB b r L)]
  rw [show List.replicate (a - 1 - i) (some true) ++ mulB b r L = mulB b r L from by
    rw [show a - 1 - i = 0 from by omega]
    simp]
  rw [mulCopy_cross4_rep i (mulB b r L) (some false)
        (List.replicate (d - 1) (some false) ++
          (some false :: (List.replicate w (none : Sym) ++ R)))]

/-- 复制遍最后一轮不停机（`2d + 2i + 6` 步，唯一终止在最后一步）。 -/
theorem mulCopy_last_no_halt (a b r w d i : Nat) (hi : i + 1 = a) (hd : 1 ≤ d) (L R : List Sym) :
    ∀ k, k < 2 * d + 2 * i + 6 →
      mulCopy.halted (mulCopy.run k ⟨(⟨0, by omega⟩ : Fin 8),
        Tape.mk (mulL a b r i L) (mulR d i w R)⟩) = false := by
  rw [show 2 * d + 2 * i + 6 = (2 * d + i + 4) + (i + 2) from by omega]
  refine no_halt_add mulCopy (2 * d + i + 4) (i + 2) _ ?_ ?_
  · exact no_halt_of_run_end mulCopy (2 * d + i + 4) _ (⟨5, by omega⟩ : Fin 8) _
      (mulCopy_last_cum a b r w d i hi hd L R) (mulCopy_ne_accept (by omega) (by omega))
      (mulCopy_ne_reject (by omega) (by omega))
  · rw [mulCopy_last_cum a b r w d i hi hd L R]
    exact mulCopy_skip5_no_halt i
      (List.replicate (b - r) (some true) ++ List.replicate r (some false) ++ (none :: (none :: L)))
      (none :: (some false :: (List.replicate (d - 1) (some false) ++
        (some false :: (List.replicate w (none : Sym) ++ R)))))

/-- **复制遍全程不停机**：整个复制遍内从不接受（唯一终止在最后一步）。
    The copy pass never halts before its final step. -/
theorem mulCopy_no_halt (a b r w d i : Nat) (hdi : i ≤ d) (hia : i + 1 ≤ a) (hwa : a - i ≤ w)
    (L R : List Sym) :
    ∀ k, k < mulLoopCost d i (a - i - 1) + (2 * (d + (a - i - 1)) + 2 * (a - 1) + 6) →
      mulCopy.halted (mulCopy.run k ⟨(⟨0, by omega⟩ : Fin 8),
        Tape.mk (mulL a b r i L) (mulR d i w R)⟩) = false := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · have hi : i = 0 := by omega
    subst hi
    subst hd0
    rcases Nat.lt_or_ge a 2 with ha1 | ha2
    · -- 源块只有一格：整个复制遍就是唯一一轮
      have ha1' : a = 1 := by omega
      subst ha1'
      exact mulCopy_last0_no_halt b r w (by omega) L R
    · -- 源块至少两格：`a - 1` 轮常规单元 + 最后一轮
      rw [show a - 0 - 1 = a - 1 from by omega]
      refine no_halt_add mulCopy (mulLoopCost 0 0 (a - 1))
        (2 * (0 + (a - 1)) + 2 * (a - 1) + 6) _ ?_ ?_
      · exact no_halt_of_run_end mulCopy (mulLoopCost 0 0 (a - 1)) _ (⟨0, by omega⟩ : Fin 8) _
          (mulCopy_loop (a - 1) a b r w 0 0 L R (by omega) (by omega) (by omega))
          (mulCopy_ne_accept (by omega) (by omega)) (mulCopy_ne_reject (by omega) (by omega))
      · rw [mulCopy_loop (a - 1) a b r w 0 0 L R (by omega) (by omega) (by omega)]
        rw [show 0 + (a - 1) = a - 1 from by omega]
        exact mulCopy_last_no_halt a b r (w - (a - 1)) (a - 1) (a - 1)
          (by omega) (by omega) L R
  · -- 副本区非空：`a - i - 1` 轮常规单元 + 最后一轮
    refine no_halt_add mulCopy (mulLoopCost d i (a - i - 1))
      (2 * (d + (a - i - 1)) + 2 * (a - 1) + 6) _ ?_ ?_
    · exact no_halt_of_run_end mulCopy (mulLoopCost d i (a - i - 1)) _ (⟨0, by omega⟩ : Fin 8) _
        (mulCopy_loop (a - i - 1) a b r w d i L R (by omega) (by omega) (by omega))
        (mulCopy_ne_accept (by omega) (by omega)) (mulCopy_ne_reject (by omega) (by omega))
    · rw [mulCopy_loop (a - i - 1) a b r w d i L R (by omega) (by omega) (by omega)]
      rw [show i + (a - i - 1) = a - 1 from by omega]
      exact mulCopy_last_no_halt a b r (w - (a - i - 1)) (d + (a - i - 1)) (a - 1)
        (by omega) (by omega) L R

@[simp] theorem mulCopy_start : mulCopy.start = (0 : Fin 8) := rfl
@[simp] theorem mulCopy_accept : mulCopy.accept = (6 : Fin 8) := rfl
@[simp] theorem mulCopy_reject : mulCopy.reject = (6 : Fin 8) := rfl
@[simp] theorem mulConsume_start : mulConsume.start = (0 : Fin 6) := rfl
@[simp] theorem mulConsume_accept : mulConsume.accept = (5 : Fin 6) := rfl
@[simp] theorem mulConsume_reject : mulConsume.reject = (5 : Fin 6) := rfl
@[simp] theorem mulRestore_start : mulRestore.start = (0 : Fin 4) := rfl
@[simp] theorem mulRestore_accept : mulRestore.accept = (3 : Fin 4) := rfl
@[simp] theorem mulRestore_reject : mulRestore.reject = (3 : Fin 4) := rfl

/-- **一轮的前半**：复制遍 + 消费一个 `B` 格（内层组合机 `seqComp mulCopy mulConsume`）。
    First half of a round: the copy pass and one consume step. -/
theorem mulCopyConsume_run (a b r w d : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b - r) (hwa : a ≤ w)
    (L R : List Sym) :
    (seqComp mulCopy mulConsume).run
      (mulLoopCost d 0 (a - 1) + (2 * (d + (a - 1)) + 2 * (a - 1) + 6) + 1 +
        (a + 2 * (b - r) + 4))
      ⟨(seqComp mulCopy mulConsume).start, Tape.mk (mulL a b r 0 L) (mulR d 0 w R)⟩
      = ⟨(seqComp mulCopy mulConsume).accept,
          Tape.mk (List.replicate a (some false) ++
              (none :: (List.replicate (b - r - 1) (some true) ++
                (List.replicate (r + 1) (some false) ++ (none :: (none :: L))))))
            (none :: (List.replicate (d + (a - 1)) (some false) ++
              (some false :: (List.replicate (w - (a - 1)) (none : Sym) ++ R))))⟩ := by
  have hcopy := mulCopy_pass a b r w d 0 (by omega) (by omega) (by omega) L R
  have hcons := mulConsume_run a (b - r) r hb L
    (List.replicate (d + (a - 1)) (some false) ++
      (some false :: (List.replicate (w - (a - 1)) (none : Sym) ++ R)))
  have hconsNh := mulConsume_no_halt a (b - r) r hb L
    (List.replicate (d + (a - 1)) (some false) ++
      (some false :: (List.replicate (w - (a - 1)) (none : Sym) ++ R)))
  exact seqComp_run mulCopy mulConsume _ _ _ _ _
    (by simpa using hcopy) (by simp) (by simpa using hcons)
    (mulCopy_no_halt a b r w d 0 (by omega) (by omega) (by omega) L R)
    (by simpa using hconsNh)

/-- 一轮的前半不停机。 The first half of a round never halts. -/
theorem mulCopyConsume_no_halt (a b r w d : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b - r) (hwa : a ≤ w)
    (L R : List Sym) :
    ∀ k, k < (mulLoopCost d 0 (a - 1) + (2 * (d + (a - 1)) + 2 * (a - 1) + 6) + 1 +
        (a + 2 * (b - r) + 4)) →
      (seqComp mulCopy mulConsume).halted
        ((seqComp mulCopy mulConsume).run k
          ⟨(seqComp mulCopy mulConsume).start, Tape.mk (mulL a b r 0 L) (mulR d 0 w R)⟩) = false := by
  have hcopy := mulCopy_pass a b r w d 0 (by omega) (by omega) (by omega) L R
  have hcons := mulConsume_no_halt a (b - r) r hb L
    (List.replicate (d + (a - 1)) (some false) ++
      (some false :: (List.replicate (w - (a - 1)) (none : Sym) ++ R)))
  exact seqComp_no_halt mulCopy mulConsume _ _ _ _
    (by simpa using hcopy) (by simp)
    (mulCopy_no_halt a b r w d 0 (by omega) (by omega) (by omega) L R)
    (by simpa using hcons)

/-! ### 一整轮 -/

/-- 一轮的步数：复制遍 + 消费一个 `B` 格 + 恢复 `A`。
    Step count of one round: copy pass, one consume step, restore. -/
def mulRoundSteps (a b r w d : Nat) : Nat :=
  (mulLoopCost d 0 (a - 1) + (2 * (d + (a - 1)) + 2 * (a - 1) + 6) + 1 +
      (a + 2 * (b - r) + 4)) + 1 + (2 * a + 3)

/-- 乘法的一轮机：`mulCopy` → `mulConsume` → `mulRestore`（状态数 `8 + 6 + 4`）。
    One round of the unary multiplication machine. -/
def mulRound : DTM (8 + 6 + 4) := seqComp (seqComp mulCopy mulConsume) mulRestore

/-- `k` 轮链式乘法的总步数：第 `j` 轮从「已消费 `j`、副本区 `j·a`、空白 `W - j·a`」出发。
    Total step count of `k` chained rounds; round `j` starts with `j` consumed cells and a
    copy area of `j·a` cells. -/
def mulRoundChainSteps : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | k + 1, a, b, W =>
      mulRoundChainSteps k a b W + (mulRoundSteps a b k (W - k * a) (k * a) + 1)

/-- **一整轮**：复制遍 + 消费一个 `B` 格 + 恢复 `A`；一轮后 B 的已消费段 `r ↦ r + 1`、
    副本区 `d ↦ d + a`、空白 `w ↦ w - a`，纸带形状与起点一致（可迭代）。
    One round: after it the consumed count is `r + 1`, the copy area `d + a` and the
    whitespace `w - a`, with the same tape shape as the round's start. -/
theorem mulRound_run (a b r w d : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b - r) (hwa : a ≤ w)
    (L R : List Sym) :
    mulRound.run (mulRoundSteps a b r w d)
      ⟨mulRound.start, Tape.mk (mulL a b r 0 L) (mulR d 0 w R)⟩
      = ⟨mulRound.accept, Tape.mk (mulL a b (r + 1) 0 L) (mulR (d + a) 0 (w - a) R)⟩ := by
  have hfirst := mulCopyConsume_run a b r w d ha hb hwa L R
  have hrest := mulRestore_run a ha
    (List.replicate (b - r - 1) (some true) ++
      (List.replicate (r + 1) (some false) ++ (none :: (none :: L))))
    (List.replicate (d + (a - 1)) (some false) ++
      (some false :: (List.replicate (w - (a - 1)) (none : Sym) ++ R)))
  have hstep := seqComp_run (seqComp mulCopy mulConsume) mulRestore _ _ _ _ _
    (by simpa using hfirst) (by simp) (by simpa using hrest)
    (mulCopyConsume_no_halt a b r w d ha hb hwa L R)
    (mulRestore_no_halt a ha _ _)
  refine hstep.trans ?_
  simp only [List.replicate_zero, List.nil_append, mulL, mulB, mulR, mulRound,
    mulRestore_accept, Config.mk.injEq, Tape.mk.injEq]
  refine ⟨by simp [seqComp, mulRestore_accept], ?_, ?_⟩
  · -- 左带：`b - r - 1` 与 `b - (r + 1)` 一致
    simp only [Nat.sub_zero, show b - (r + 1) = b - r - 1 from by omega]
    rw [List.append_assoc]
  · -- 右带：`replicate` 的算术
    rw [show d + (a - 1) = d + a - 1 from by omega]
    rw [replicate_succ_append (d + a - 1) (some false)
      (List.replicate (w - (a - 1)) (none : Sym) ++ R)]
    rw [show d + a - 1 + 1 = d + a from by omega]
    rw [show w - (a - 1) = w - a + 1 from by omega]
    rw [show w - a + 1 = (w - a) + 1 from by omega, List.replicate_succ]
    rw [List.cons_append]

/-- **一轮全程不停机**：本轮的 `mulRoundSteps` 步内从不接受。
    One round never halts before its final step. -/
theorem mulRound_no_halt (a b r w d : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b - r) (hwa : a ≤ w)
    (L R : List Sym) :
    ∀ k, k < mulRoundSteps a b r w d →
      mulRound.halted
        (mulRound.run k ⟨mulRound.start, Tape.mk (mulL a b r 0 L) (mulR d 0 w R)⟩) = false := by
  have hfirst := mulCopyConsume_run a b r w d ha hb hwa L R
  have hrest := mulRestore_run a ha
    (List.replicate (b - r - 1) (some true) ++
      (List.replicate (r + 1) (some false) ++ (none :: (none :: L))))
    (List.replicate (d + (a - 1)) (some false) ++
      (some false :: (List.replicate (w - (a - 1)) (none : Sym) ++ R)))
  have hrestNh := mulRestore_no_halt a ha
    (List.replicate (b - r - 1) (some true) ++
      (List.replicate (r + 1) (some false) ++ (none :: (none :: L))))
    (List.replicate (d + (a - 1)) (some false) ++
      (some false :: (List.replicate (w - (a - 1)) (none : Sym) ++ R)))
  have hnh := seqComp_no_halt (seqComp mulCopy mulConsume) mulRestore _ _ _ _
    (by simpa using hfirst) (by simp)
    (mulCopyConsume_no_halt a b r w d ha hb hwa L R)
    (by simpa using hrestNh)
  simpa [mulRound, mulRoundSteps, seqComp] using hnh

/-! ### 链式乘法轮机与统一相位 -/

/-- 链式乘法轮机：`mulRound` 的接受态原地跳回起点（状态数 `8 + 6 + 4 + 1`，18 为不可达停机态）。
    The chained multiplication machine: `mulRound`'s accept state jumps back to the start
    (state count `8 + 6 + 4 + 1`, with 18 an unreachable terminal state). -/
def mulChained : DTM (8 + 6 + 4 + 1) where
  step := fun s a =>
    if s.val = 17 then ((⟨0, by omega⟩ : Fin (8 + 6 + 4 + 1)), a, Dir.stay)
    else if h : s.val < 18 then
      let r := mulRound.step ⟨s.val, h⟩ a
      (Fin.castLE (by omega) r.1, r.2)
    else (s, a, Dir.stay)
  start := 0
  accept := 18
  reject := 18

/-- 链式机在 `mulRound` 接受态上的转移：原地回到起始态（写回读到的符号、不动）。
    The chained transition at `mulRound`'s accept state: back to the start, tape untouched. -/
theorem mulChained_step_accept (a : Sym) :
    mulChained.step (Fin.castLE (by omega) mulRound.accept) a
      = ((⟨0, by omega⟩ : Fin (8 + 6 + 4 + 1)), a, Dir.stay) := by
  have hval : mulRound.accept.val = 17 := rfl
  simp only [mulChained, Fin.val_castLE]
  rw [if_pos hval]

/-- 链式机的转移在 `mulRound` 的非接受状态上照抄 `mulRound`。
    The chained machine copies `mulRound`'s transitions away from its accept state. -/
theorem mulChained_step_castLE (s : Fin 18) (a : Sym) (hne : s ≠ mulRound.accept) :
    mulChained.step (Fin.castLE (by omega) s) a
      = (Fin.castLE (by omega) (mulRound.step s a).1, (mulRound.step s a).2) := by
  have hv : s.val ≠ 17 := by
    intro h
    apply hne
    have hacc : mulRound.accept = (⟨17, by omega⟩ : Fin 18) := rfl
    rw [hacc]
    exact Fin.ext h
  have hlt : s.val < 18 := s.isLt
  simp only [mulChained, Fin.val_castLE]
  rw [if_neg (by simpa using hv)]
  rw [dif_pos hlt]

/-- 链式机的接受/拒绝占位态不会与左侧状态重合（左侧状态的值 < 18）。
    The placeholder terminal state never coincides with a `mulRound`-side state. -/
theorem mulChained_halt_castLE (s : Fin 18) :
    mulChained.accept ≠ Fin.castLE (by omega) s
      ∧ mulChained.reject ≠ Fin.castLE (by omega) s := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_castLE] at hv
    have h2 : mulChained.accept.val = 18 := rfl
    rw [h2] at hv
    have h3 := s.isLt
    omega
  · intro h
    have hv := congrArg Fin.val h
    rw [Fin.val_castLE] at hv
    have h2 : mulChained.reject.val = 18 := rfl
    rw [h2] at hv
    have h3 := s.isLt
    omega

/-- 链式机照搬 `mulRound` 的任意一段运行（`mulRound` 在这段内不停机）。
    Chained runs mirror `mulRound` runs as long as `mulRound` does not halt. -/
theorem mulChained_run_embed (n : Nat) (c : Config 18)
    (hnh : ∀ k, k < n → mulRound.halted (mulRound.run k c) = false) :
    mulChained.run n ⟨Fin.castLE (by omega) c.state, c.tape⟩ =
      ⟨Fin.castLE (by omega) (mulRound.run n c).state, (mulRound.run n c).tape⟩ :=
  run_embed mulRound mulChained (Fin.castLE (by omega))
    (fun s a ha _ => mulChained_step_castLE s a ha)
    (fun s _ _ => mulChained_halt_castLE s) n c hnh

/-- **链式一轮**：跑完一轮乘法后**自动回到起始态**，共 `mulRoundSteps a b r w d + 1` 步。
    One chained round: same tape effect as `mulRound`, but back in the start state. -/
theorem mulChained_round (a b r w d : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b - r) (hwa : a ≤ w)
    (L R : List Sym) :
    mulChained.run (mulRoundSteps a b r w d + 1)
      ⟨mulChained.start, Tape.mk (mulL a b r 0 L) (mulR d 0 w R)⟩
      = ⟨mulChained.start, Tape.mk (mulL a b (r + 1) 0 L) (mulR (d + a) 0 (w - a) R)⟩ := by
  show mulChained.run (mulRoundSteps a b r w d + 1)
      ⟨Fin.castLE (by omega) mulRound.start,
        Tape.mk (mulL a b r 0 L) (mulR d 0 w R)⟩ =
    ⟨mulChained.start, Tape.mk (mulL a b (r + 1) 0 L) (mulR (d + a) 0 (w - a) R)⟩
  have hemb := mulChained_run_embed (mulRoundSteps a b r w d)
    ⟨mulRound.start, Tape.mk (mulL a b r 0 L) (mulR d 0 w R)⟩
    (mulRound_no_halt a b r w d ha hb hwa L R)
  rw [mulRound_run a b r w d ha hb hwa L R] at hemb
  have hemb' : mulChained.run (mulRoundSteps a b r w d)
      ⟨Fin.castLE (by omega) mulRound.start,
        Tape.mk (mulL a b r 0 L) (mulR d 0 w R)⟩ =
      ⟨Fin.castLE (by omega) mulRound.accept,
        Tape.mk (mulL a b (r + 1) 0 L) (mulR (d + a) 0 (w - a) R)⟩ := by
    simpa using hemb
  have hnh2 : mulChained.halted
      ⟨Fin.castLE (by omega) mulRound.accept,
        Tape.mk (mulL a b (r + 1) 0 L) (mulR (d + a) 0 (w - a) R)⟩ = false := by
    rw [DTM.halted, Bool.or_eq_false_iff]
    refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
    · intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_castLE] at hv
      have h2 : mulRound.accept.val = 17 := rfl
      rw [h2] at hv
      have h3 : mulChained.accept.val = 18 := rfl
      rw [h3] at hv
      exact absurd hv (by decide)
    · intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_castLE] at hv
      have h2 : mulRound.accept.val = 17 := rfl
      rw [h2] at hv
      have h3 : mulChained.reject.val = 18 := rfl
      rw [h3] at hv
      exact absurd hv (by decide)
  have hstep : mulChained.stepConfig
      ⟨Fin.castLE (by omega) mulRound.accept,
        Tape.mk (mulL a b (r + 1) 0 L) (mulR (d + a) 0 (w - a) R)⟩ =
      ⟨(⟨0, by omega⟩ : Fin (8 + 6 + 4 + 1)),
        Tape.mk (mulL a b (r + 1) 0 L) (mulR (d + a) 0 (w - a) R)⟩ := by
    rw [DTM.stepConfig, mulChained_step_accept]
    simp [Tape.write_read, Tape.move]
  rw [DTM.run_add mulChained (mulRoundSteps a b r w d) 1, hemb']
  rw [DTM.run_succ_of_not_halted mulChained 0 _ hnh2]
  simpa [DTM.run, mulChained] using hstep

/-- **多轮链式乘法**：`mulChained` 自动连跑 `k` 轮，已消费格 `k`、副本区 `k·a`、
    空白 `W - k·a`，纸带形状全程不变、机器全程回到起点。
    `k` chained rounds: `k` consumed cells, copy area `k·a`, whitespace `W - k·a`; the tape
    shape is preserved and the machine returns to the start state each round. -/
theorem mulChained_rounds (k a b W : Nat) (ha : 1 ≤ a) (hk : k ≤ b) (hW : k * a ≤ W)
    (L R : List Sym) :
    mulChained.run (mulRoundChainSteps k a b W)
      ⟨mulChained.start, Tape.mk (mulL a b 0 0 L) (mulR 0 0 W R)⟩
      = ⟨mulChained.start, Tape.mk (mulL a b k 0 L) (mulR (k * a) 0 (W - k * a) R)⟩ := by
  induction k with
  | zero =>
      simp [mulRoundChainSteps, DTM.run]
  | succ k ih =>
      -- 把 `(k+1)·a` 写成 `k·a + a`，其余算术就都是 Presburger 了
      have hstep : (k + 1) * a = k * a + a := Nat.succ_mul k a
      have hkW : k * a ≤ W := by
        have h' : k * a + a ≤ W := by rw [← hstep]; exact hW
        exact Nat.le_trans (Nat.le_add_right (k * a) a) h'
      have hwa : a ≤ W - k * a :=
        Nat.le_sub_of_add_le (by rw [Nat.add_comm]; rw [← hstep]; exact hW)
      rw [mulRoundChainSteps,
        DTM.run_add mulChained (mulRoundChainSteps k a b W)
          (mulRoundSteps a b k (W - k * a) (k * a) + 1),
        ih (show k ≤ b from by omega) hkW,
        mulChained_round a b k (W - k * a) (k * a) ha (by omega) hwa L R]
      rw [show k * a + a = (k + 1) * a from by omega]
      rw [show W - k * a - a = W - (k + 1) * a from by omega]

/-- 统一相位机（3 状态，2 为停机态）：右行越过 A 的 `some true`、跨过 `sepA`，
    再把副本区的 `some false` 逐格改回 `some true`，遇前沿空白接受。
    The unify-phase machine: walk right over `A`'s trues, cross `sepA`, flip the copy area's
    falses back to trues, and accept on the frontier blank. -/
def mulFinish : DTM 3 where
  step := fun s a =>
    match s.val with
    | 0 => (match a with
       | some true => (⟨0, by omega⟩, some true, Dir.right)
       | none => (⟨1, by omega⟩, none, Dir.right)
       | some false => (⟨1, by omega⟩, some false, Dir.right))
    | 1 => (match a with
       | some false => (⟨1, by omega⟩, some true, Dir.right)
       | none => (⟨2, by omega⟩, none, Dir.stay)
       | some true => (⟨1, by omega⟩, some true, Dir.right))
    | _ => (s, a, Dir.stay)
  start := 0
  accept := 2
  reject := 2

/-- 非 2 状态一律不停机。 States other than 2 never halt. -/
theorem mulFinish_halted_ne (st : Nat) (hst : st < 3) (h : st ≠ 2) (t : Tape) :
    mulFinish.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show mulFinish.accept.val = 2 from rfl] at hv
    exact h hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show mulFinish.reject.val = 2 from rfl] at hv
    exact h hv

/-- `mulFinish` 的单步运行套路。 The one-step idiom for `mulFinish`. -/
theorem estepMF (st : Nat) (hst : st < 3) (a : Sym) (q' : Fin 3) (s : Sym) (d : Dir)
    (h : mulFinish.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 2) :
    mulFinish.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (mulFinish_halted_ne st hst hne _)]
  exact stepConfig_of_step mulFinish ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- 状态 1 把 `d` 个 `some false` 逐格改回 `some true`（头停在随后的空白上）。
    State 1 flips `d` falses back to trues and stops on the following blank. -/
theorem mulFinish_conv : ∀ (d : Nat) (P R : List Sym),
    mulFinish.run d
      ⟨(⟨1, by omega⟩ : Fin 3),
        Tape.mk P (List.replicate d (some false) ++ (none :: R))⟩
      = ⟨(⟨1, by omega⟩ : Fin 3),
          Tape.mk (List.replicate d (some true) ++ P) (none :: R)⟩
  | 0, P, R => by
      simp [DTM.run]
  | d + 1, P, R => by
      conv =>
        lhs
        rw [List.replicate_succ, List.cons_append]
        rw [show d + 1 = 1 + d from by omega]
      rw [DTM.run_add mulFinish 1 d]
      rw [estepMF 1 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [mulFinish_conv d (some true :: P) R]
      rw [replicate_succ_append d (some true) P]

/-- **统一副本区**：`d + 3` 步——越过 A 最右格上的 `some true`、跨过 `sepA`，
    把 `d` 个副本格 `some false` 改回 `some true`，遇前沿空白接受。
    Unify the copy area in `d + 3` steps: over A's rightmost true, across `sepA`, flip the
    `d` copy cells, and accept on the frontier blank. -/
theorem mulFinish_run (d : Nat) (hd : 1 ≤ d) (A R : List Sym) :
    mulFinish.run (d + 3)
      ⟨(⟨0, by omega⟩ : Fin 3),
        Tape.mk A (some true :: (none :: (List.replicate d (some false) ++ (none :: R))))⟩
      = ⟨(⟨2, by omega⟩ : Fin 3),
          Tape.mk (List.replicate d (some true) ++ (none :: (some true :: A)))
            (none :: R)⟩ := by
  rw [show d + 3 = 1 + (1 + (d + 1)) from by omega]
  rw [DTM.run_add mulFinish 1 (1 + (d + 1))]
  -- 状态 0：越过 A 最右格
  rw [estepMF 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  -- 状态 0：跨过 `sepA`
  rw [DTM.run_add mulFinish 1 (d + 1)]
  rw [estepMF 0 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape
  -- 状态 1：逐格统一副本区
  rw [DTM.run_add mulFinish d 1]
  rw [mulFinish_conv d (none :: (some true :: A)) R]
  -- 状态 1：遇前沿空白接受
  rw [estepMF 1 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- **乘法整机规格（纸带级）**：先跑 `b` 轮链式轮（副本区 `b·a` 格），再用统一相位把副本
    区改回 `some true`，终态是 `replicate (b·a) true` 的 unary 块。
    End-to-end tape-level spec: `b` chained rounds then the unify phase, ending with a unary
    block of `b·a` trues. -/
theorem mulChained_finish_run (a b W : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b) (hW : b * a ≤ W)
    (L R : List Sym) :
    mulFinish.run (b * a + 3)
      ⟨mulFinish.start,
        (mulChained.run (mulRoundChainSteps b a b W)
          ⟨mulChained.start, Tape.mk (mulL a b 0 0 L) (mulR 0 0 W R)⟩).tape⟩
      = ⟨mulFinish.accept,
          Tape.mk (List.replicate (b * a) (some true) ++
              (none :: (some true :: mulL a b b 0 L)))
            (none :: (List.replicate (W - b * a) (none : Sym) ++ R))⟩ := by
  have hch := mulChained_rounds b a b W ha (by omega) hW L R
  rw [hch]
  have hrun := mulFinish_run (b * a)
    (show 1 ≤ b * a from Nat.mul_pos (by omega) (by omega)) (mulL a b b 0 L)
    (List.replicate (W - b * a) (none : Sym) ++ R)
  simpa [mulFinish, mulR, List.replicate_zero, List.nil_append] using hrun

/-! ### B 耗尽检测相位（乘法链的「继续 / 收尾」判据） -/

/-- 耗尽检测机（6 状态）：从 A 最右格出发，左行跳过 A 的 `some true`、跨过 A 与 B 之间的
    空白，读 B 的最近格——`some true` ⇒ 还有未消费格（回到 A 最右格，接受态 4）；
    `some false` ⇒ B 已耗尽（停在 B 最近格，拒绝态 5）。
    The exhaustion-check machine: from A's rightmost cell, walk left over A's trues, cross the
    blank between A and B, and read B's nearest cell — `some true` means work remains (back to
    A's rightmost cell, accept state 4); `some false` means B is exhausted (reject state 5). -/
def mulCheck : DTM 6 where
  step := fun s a =>
    match s.val with
    | 0 => (match a with
       | some true => (⟨0, by omega⟩, some true, Dir.left)
       | none => (⟨1, by omega⟩, none, Dir.left)
       | some false => (⟨0, by omega⟩, some false, Dir.left))
    | 1 => (match a with
       | some true => (⟨2, by omega⟩, some true, Dir.right)
       | some false => (⟨5, by omega⟩, some false, Dir.stay)
       | none => (⟨5, by omega⟩, none, Dir.stay))
    | 2 => (match a with
       | none => (⟨3, by omega⟩, none, Dir.right)
       | _ => (⟨3, by omega⟩, a, Dir.right))
    | 3 => (match a with
       | some true => (⟨3, by omega⟩, some true, Dir.right)
       | none => (⟨4, by omega⟩, none, Dir.left)
       | some false => (⟨4, by omega⟩, some false, Dir.left))
    | _ => (s, a, Dir.stay)
  start := 0
  accept := 4
  reject := 5

/-- 非 4/5 状态一律不停机。 States other than 4 and 5 never halt. -/
theorem mulCheck_halted_ne (st : Nat) (hst : st < 6) (h4 : st ≠ 4) (h5 : st ≠ 5) (t : Tape) :
    mulCheck.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show mulCheck.accept.val = 4 from rfl] at hv
    exact h4 hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show mulCheck.reject.val = 5 from rfl] at hv
    exact h5 hv

/-- `mulCheck` 的单步运行套路。 The one-step idiom for `mulCheck`. -/
theorem estepMK (st : Nat) (hst : st < 6) (a : Sym) (q' : Fin 6) (s : Sym) (d : Dir)
    (h : mulCheck.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (h4 : st ≠ 4) (h5 : st ≠ 5) :
    mulCheck.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (mulCheck_halted_ne st hst h4 h5 _)]
  exact stepConfig_of_step mulCheck ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- 状态 0 左行跳过 `m` 个 `some true`（把格写回右带、原样保留）。
    State 0 walks left over `m` trues, writing them back unchanged. -/
theorem mulCheck_skipA : ∀ (m : Nat) (P R : List Sym),
    mulCheck.run m
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate m (some true) ++ P) (some true :: R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk P (List.replicate m (some true) ++ (some true :: R))⟩
  | 0, P, R => by
      simp [DTM.run]
  | m + 1, P, R => by
      conv =>
        lhs
        rw [List.replicate_succ, List.cons_append]
        rw [show m + 1 = 1 + m from by omega]
      rw [DTM.run_add mulCheck 1 m]
      rw [estepMK 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      rw [mulCheck_skipA m P (some true :: R)]
      rw [replicate_succ_append m (some true) (some true :: R)]

/-- 状态 3 右行跳过 `m` 个 `some true` 并停在空白上（`m` 步）。
    State 3 walks right over `m` trues and stops on the blank, in `m` steps. -/
theorem mulCheck_skipR : ∀ (m : Nat) (P R : List Sym),
    mulCheck.run m
      ⟨(⟨3, by omega⟩ : Fin 6),
        Tape.mk P (List.replicate m (some true) ++ (none :: R))⟩
      = ⟨(⟨3, by omega⟩ : Fin 6),
          Tape.mk (List.replicate m (some true) ++ P) (none :: R)⟩
  | 0, P, R => by
      simp [DTM.run]
  | m + 1, P, R => by
      conv =>
        lhs
        rw [List.replicate_succ, List.cons_append]
        rw [show m + 1 = 1 + m from by omega]
      rw [DTM.run_add mulCheck 1 m]
      rw [estepMK 3 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega) (by omega)]
      etape
      rw [mulCheck_skipR m (some true :: P) R]
      rw [replicate_succ_append m (some true) P]

/-- **检测「B 还有未消费格」**：`2a + 4` 步后回到 A 的最右格（接受态），纸带原样。
    `2a + 4` steps back to A's rightmost cell (accept state), tape unchanged. -/
theorem mulCheck_continue_run (a : Nat) (ha : 1 ≤ a) (P R : List Sym) :
    mulCheck.run (2 * a + 4)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some true :: P)))
          (some true :: (none :: R))⟩
      = ⟨(⟨4, by omega⟩ : Fin 6),
          Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some true :: P)))
            (some true :: (none :: R))⟩ := by
  rcases a with _ | a'
  · omega
  simp only [Nat.add_sub_cancel]
  -- 步数分解：(a-1) + 1(空白) + 1(跨空白) + 1(折返) + 1(跨回) + a(跳过 A) + 1(退回)
  rw [show 2 * (a' + 1) + 4 = a' + (1 + (1 + (1 + (1 + ((a' + 1) + 1))))) from by omega]
  -- 状态 0：左行跳过 A 的 `a'` 格（头落在 A 最左格上）
  rw [DTM.run_add mulCheck a' (1 + (1 + (1 + (1 + ((a' + 1) + 1)))))]
  rw [mulCheck_skipA a' (none :: (some true :: P)) (none :: R)]
  -- 把 `replicate` 的单元提到表头，便于「读到的就是 `some true`」的字面匹配
  rw [← cons_replicate_append (some true) a' (none :: R)]
  -- 状态 0：再左移一步，头落在 A 与 B 之间的空白上
  rw [DTM.run_add mulCheck 1 (1 + (1 + (1 + ((a' + 1) + 1))))]
  rw [estepMK 0 (by omega) (some true) _ _ _ (by rfl)
    _ _ (by omega) (by omega)]
  etape
  -- 状态 0：跨过空白，头落在 B 的最近格上
  rw [DTM.run_add mulCheck 1 (1 + (1 + ((a' + 1) + 1)))]
  rw [estepMK 0 (by omega) none _ _ _ (by rfl) _ _ (by omega) (by omega)]
  etape
  -- 状态 1：读到 `some true` ⇒ 折返
  rw [DTM.run_add mulCheck 1 (1 + ((a' + 1) + 1))]
  rw [estepMK 1 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega) (by omega)]
  etape
  -- 状态 2：跨回空白进 A 的最左格
  rw [DTM.run_add mulCheck 1 ((a' + 1) + 1)]
  rw [estepMK 2 (by omega) none _ _ _ (by rfl) _ _ (by omega) (by omega)]
  etape
  -- 状态 3：右行跳过 A 的全部格，再退回最右格
  rw [DTM.run_add mulCheck (a' + 1) 1]
  rw [cons_replicate_append (some true) a' (none :: R)]
  rw [replicate_succ_append a' (some true) (none :: R)]
  rw [mulCheck_skipR (a' + 1) (none :: (some true :: P)) R]
  rw [estepMK 3 (by omega) none _ _ _ (by rfl)
    (List.replicate (a' + 1) (some true) ++ (none :: (some true :: P))) R
    (by omega) (by omega)]
  etape
  rw [List.replicate_succ]
  simp

/-- **检测「B 已耗尽」**：`a + 2` 步后停在 B 的最近格上（拒绝态），纸带原样。
    `a + 2` steps to B's nearest cell (reject state), tape unchanged. -/
theorem mulCheck_done_run (a : Nat) (ha : 1 ≤ a) (P R : List Sym) :
    mulCheck.run (a + 2)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some false :: P)))
          (some true :: (none :: R))⟩
      = ⟨(⟨5, by omega⟩ : Fin 6),
          Tape.mk P (some false :: (none ::
            (List.replicate (a - 1) (some true) ++ (some true :: (none :: R)))))⟩ := by
  rcases a with _ | a'
  · omega
  simp only [Nat.add_sub_cancel]
  -- 步数分解：(a-1) + 1(空白) + 1(跨空白) + 1(读到 `some false` 停机)
  rw [show a' + 1 + 2 = a' + (1 + (1 + 1)) from by omega]
  rw [DTM.run_add mulCheck a' (1 + (1 + 1))]
  rw [mulCheck_skipA a' (none :: (some false :: P)) (none :: R)]
  -- 把 `replicate` 的单元提到表头，便于「读到的就是 `some true`」的字面匹配
  rw [← cons_replicate_append (some true) a' (none :: R)]
  rw [DTM.run_add mulCheck 1 (1 + 1)]
  rw [estepMK 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega) (by omega)]
  etape
  rw [DTM.run_add mulCheck 1 1]
  rw [estepMK 0 (by omega) none _ _ _ (by rfl) _ _ (by omega) (by omega)]
  etape
  rw [estepMK 1 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega) (by omega)]
  etape

/-! ### 一轮 + 检测的合成（自动收尾循环的归纳步） -/

/-- **一轮之后再做检测**：一轮结束后（B 还有未消费格，`r + 2 ≤ b`），检测相位把机器带回
    下一轮的起点（A 最右格），因此「轮 + 检测」构成一个可迭代的循环步。
    One round followed by the check: when `B` still has unconsumed cells (`r + 2 ≤ b`), the
    check phase returns to the next round's start, so "round + check" is one loop step. -/
theorem mulRoundCheck_run (a b r w d : Nat) (ha : 1 ≤ a) (hb : r + 2 ≤ b) (hwa : a ≤ w)
    (L R : List Sym) :
    mulCheck.run (2 * a + 4)
      ⟨mulCheck.start,
        (mulRound.run (mulRoundSteps a b r w d)
          ⟨mulRound.start, Tape.mk (mulL a b r 0 L) (mulR d 0 w R)⟩).tape⟩
      = ⟨mulCheck.accept,
          Tape.mk (mulL a b (r + 1) 0 L) (mulR (d + a) 0 (w - a) R)⟩ := by
  have hround := mulRound_run a b r w d ha (by omega) hwa L R
  -- 终点的左带里 B 的最近格是 `some true`：把 `replicate (b - (r+1))` 拆出头
  have hb1 : 1 ≤ b - (r + 1) := by omega
  rcases hb' : b - (r + 1) with _ | k
  · omega
  have hrun := mulCheck_continue_run a ha
    (List.replicate k (some true) ++
      (List.replicate (r + 1) (some false) ++ (none :: (none :: L))))
    (List.replicate (d + a) (some false) ++
      (none :: (List.replicate (w - a) (none : Sym) ++ R)))
  -- 目标里的「轮终点」形态与检测的前提形态对齐
  rw [hround]
  have hshape : mulB b (r + 1) L
      = none :: (some true :: (List.replicate k (some true) ++
          (List.replicate (r + 1) (some false) ++ (none :: (none :: L))))) := by
    simp only [mulB]
    rw [hb', List.replicate_succ]
    simp only [List.cons_append, List.append_assoc]
  simp only [mulL, mulR, List.replicate_zero, List.nil_append]
  rw [hshape]
  exact hrun

/-! ### 收尾相位 `mulFinal`（从 B 的耗尽位置走到副本区并统一） -/

/-- 收尾相位机（4 状态，3 为停机态）：耗尽检测停在 B 的最近格上，本机右行跨过分隔空白、
    跳过 A 的全部 `some true`、跨过 `sepA`，再把副本区的 `some false` 逐格改回 `some true`，
    遇前沿空白接受。
    The final phase machine: starting on B's nearest (exhausted) cell, walk right across the
    blank and all of A, cross `sepA`, flip the copy area's falses back to trues, and accept on
    the frontier blank. -/
def mulFinal : DTM 4 where
  step := fun s a =>
    match s.val with
    | 0 => (match a with
       | some false => (⟨0, by omega⟩, some false, Dir.right)
       | none => (⟨1, by omega⟩, none, Dir.right)
       | some true => (⟨1, by omega⟩, some true, Dir.right))
    | 1 => (match a with
       | some true => (⟨1, by omega⟩, some true, Dir.right)
       | none => (⟨2, by omega⟩, none, Dir.right)
       | some false => (⟨2, by omega⟩, some false, Dir.right))
    | 2 => (match a with
       | some false => (⟨2, by omega⟩, some true, Dir.right)
       | none => (⟨3, by omega⟩, none, Dir.stay)
       | some true => (⟨2, by omega⟩, some true, Dir.right))
    | _ => (s, a, Dir.stay)
  start := 0
  accept := 3
  reject := 3

/-- 非 3 状态一律不停机。 States other than 3 never halt. -/
theorem mulFinal_halted_ne (st : Nat) (hst : st < 4) (h : st ≠ 3) (t : Tape) :
    mulFinal.halted ⟨⟨st, hst⟩, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show mulFinal.accept.val = 3 from rfl] at hv
    exact h hv
  · intro hh
    have hv := congrArg Fin.val hh
    rw [show mulFinal.reject.val = 3 from rfl] at hv
    exact h hv

/-- `mulFinal` 的单步运行套路。 The one-step idiom for `mulFinal`. -/
theorem estepMF2 (st : Nat) (hst : st < 4) (a : Sym) (q' : Fin 4) (s : Sym) (d : Dir)
    (h : mulFinal.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 3) :
    mulFinal.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (mulFinal_halted_ne st hst hne _)]
  exact stepConfig_of_step mulFinal ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- 状态 1 右行跳过 `m` 个 `some true` 并停在空白上（`m` 步）。
    State 1 walks right over `m` trues and stops on the blank, in `m` steps. -/
theorem mulFinal_skipT : ∀ (m : Nat) (P R : List Sym),
    mulFinal.run m
      ⟨(⟨1, by omega⟩ : Fin 4),
        Tape.mk P (List.replicate m (some true) ++ (none :: R))⟩
      = ⟨(⟨1, by omega⟩ : Fin 4),
          Tape.mk (List.replicate m (some true) ++ P) (none :: R)⟩
  | 0, P, R => by
      simp [DTM.run]
  | m + 1, P, R => by
      conv =>
        lhs
        rw [List.replicate_succ, List.cons_append]
        rw [show m + 1 = 1 + m from by omega]
      rw [DTM.run_add mulFinal 1 m]
      rw [estepMF2 1 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [mulFinal_skipT m (some true :: P) R]
      rw [replicate_succ_append m (some true) P]

/-- 状态 2 把 `d` 个 `some false` 逐格改回 `some true`（头停在随后的空白上）。
    State 2 flips `d` falses back to trues and stops on the following blank. -/
theorem mulFinal_conv : ∀ (d : Nat) (P R : List Sym),
    mulFinal.run d
      ⟨(⟨2, by omega⟩ : Fin 4),
        Tape.mk P (List.replicate d (some false) ++ (none :: R))⟩
      = ⟨(⟨2, by omega⟩ : Fin 4),
          Tape.mk (List.replicate d (some true) ++ P) (none :: R)⟩
  | 0, P, R => by
      simp [DTM.run]
  | d + 1, P, R => by
      conv =>
        lhs
        rw [List.replicate_succ, List.cons_append]
        rw [show d + 1 = 1 + d from by omega]
      rw [DTM.run_add mulFinal 1 d]
      rw [estepMF2 2 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [mulFinal_conv d (some true :: P) R]
      rw [replicate_succ_append d (some true) P]

/-- **收尾整段**：`a + d + 4` 步——从 B 的最近格右行跨空白、跳过 A 的全部格、跨 `sepA`，
    把 `d` 个副本格改回 `some true`，遇前沿空白接受。
    The whole final phase in `a + d + 4` steps. -/
theorem mulFinal_run (a d : Nat) (ha : 1 ≤ a) (hd : 1 ≤ d) (P R : List Sym) :
    mulFinal.run (a + d + 4)
      ⟨(⟨0, by omega⟩ : Fin 4),
        Tape.mk P (some false :: (none ::
          (List.replicate (a - 1) (some true) ++
            (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩
      = ⟨(⟨3, by omega⟩ : Fin 4),
          Tape.mk (List.replicate d (some true) ++
            (none :: (List.replicate a (some true) ++ (none :: (some false :: P)))))
            (none :: R)⟩ := by
  rcases a with _ | a'
  · omega
  simp only [Nat.add_sub_cancel]
  -- 步数分解：1（离开 B 最近格）+ 1（跨空白进 A）+ (a'+1)（跳过 A）+ 1（跨 `sepA`）+ d + 1
  rw [show a' + 1 + d + 4 = 1 + (1 + ((a' + 1) + (1 + (d + 1)))) from by omega]
  rw [DTM.run_add mulFinal 1 (1 + ((a' + 1) + (1 + (d + 1))))]
  -- 状态 0：离开 B 的最近格，落在空白上
  rw [estepMF2 0 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  etape
  -- 状态 0：跨过空白，进 A 的最左格
  rw [DTM.run_add mulFinal 1 ((a' + 1) + (1 + (d + 1)))]
  rw [estepMF2 0 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape
  -- 状态 1：右行跳过 A 的全部格（`replicate a' ++ some true = replicate (a'+1)`）
  rw [DTM.run_add mulFinal (a' + 1) (1 + (d + 1))]
  rw [replicate_succ_append a' (some true)
    (none :: (List.replicate d (some false) ++ (none :: R)))]
  rw [mulFinal_skipT (a' + 1) (none :: (some false :: P))
    (List.replicate d (some false) ++ (none :: R))]
  -- 状态 1：跨过 `sepA`，进副本区首格
  rw [DTM.run_add mulFinal 1 (d + 1)]
  rw [estepMF2 1 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape
  -- 状态 2：逐格统一副本区
  rw [DTM.run_add mulFinal d 1]
  rw [mulFinal_conv d
    (none :: (List.replicate (a' + 1) (some true) ++ (none :: (some false :: P)))) R]
  -- 状态 2：遇前沿空白接受
  rw [estepMF2 2 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  simp [Tape.write, Tape.move]

/-! ### 乘法整机 `mulMachine`（轮 → 检测 → 继续 / 收尾） -/

/-- 嵌入映射：轮机状态（0..17）原样进入整机。
    Embedding of the round machine's states into the whole machine. -/
def mulEmbR (s : Fin 18) : Fin 28 := Fin.castLE (by omega) s

/-- 嵌入映射：检测机状态（0..5）→ 18..23。 -/
def mulEmbC (s : Fin 6) : Fin 28 := ⟨18 + s.val, by have := s.isLt; omega⟩

/-- 嵌入映射：收尾机状态（0..3）→ 24..27。 -/
def mulEmbF (s : Fin 4) : Fin 28 := ⟨24 + s.val, by have := s.isLt; omega⟩

/-- 乘法整机（28 状态，27 为唯一停机态）：
    0..17 = 一轮（`mulRound`）、18..23 = 耗尽检测（`mulCheck`）、24..27 = 收尾（`mulFinal`）。
    转移改接：`mulRound` 的接受态 17 → 检测入口 18；检测的继续态 22 → 轮起点 0；
    检测的耗尽态 23 → 收尾入口 24。
    The whole multiplication machine (28 states, 27 the only halting state). Round states are
    states 0..17; the exhaustion check 18..23; the final phase 24..27. Redirects: the round's
    accept (17) → check entry (18); the check's continue state (22) → round start (0); the
    check's exhausted state (23) → final entry (24). -/
def mulMachine : DTM 28 where
  step := fun s a =>
    if s.val = 17 then ((⟨18, by omega⟩ : Fin 28), a, Dir.stay)
    else if s.val = 22 then ((⟨0, by omega⟩ : Fin 28), a, Dir.stay)
    else if s.val = 23 then ((⟨24, by omega⟩ : Fin 28), a, Dir.stay)
    else if h : s.val < 18 then
      let r := mulRound.step ⟨s.val, h⟩ a
      (mulEmbR r.1, r.2)
    else if h : s.val < 24 then
      let r := mulCheck.step ⟨s.val - 18, by omega⟩ a
      (mulEmbC r.1, r.2)
    else
      let r := mulFinal.step ⟨s.val - 24, by omega⟩ a
      (mulEmbF r.1, r.2)
  start := 0
  accept := 27
  reject := 27

/-- 整机在轮机状态上照抄 `mulRound`（除接受态 17 外）。
    The whole machine mirrors `mulRound` on round states except its accept state. -/
theorem mulMachine_step_round (s : Fin 18) (a : Sym) (hne : s ≠ mulRound.accept) :
    mulMachine.step (mulEmbR s) a
      = (mulEmbR (mulRound.step s a).1, (mulRound.step s a).2) := by
  have hv : s.val ≠ 17 := by
    intro h
    apply hne
    have hacc : mulRound.accept = (⟨17, by omega⟩ : Fin 18) := rfl
    rw [hacc]
    exact Fin.ext h
  simp only [mulMachine, mulEmbR, Fin.val_castLE]
  rw [if_neg (by simpa using hv)]
  rw [if_neg (by have := s.isLt; omega)]
  rw [if_neg (by have := s.isLt; omega)]
  rw [dif_pos s.isLt]

/-- 整机在检测机状态上照抄 `mulCheck`（除其接受态 4 与拒绝态 5 外）。
    The whole machine mirrors `mulCheck` on check states except 4 and 5. -/
theorem mulMachine_step_check (s : Fin 6) (a : Sym)
    (hne4 : s ≠ mulCheck.accept) (hne5 : s ≠ mulCheck.reject) :
    mulMachine.step (mulEmbC s) a
      = (mulEmbC (mulCheck.step s a).1, (mulCheck.step s a).2) := by
  have hv4 : s.val ≠ 4 := by
    intro h
    apply hne4
    have hacc : mulCheck.accept = (⟨4, by omega⟩ : Fin 6) := rfl
    rw [hacc]
    exact Fin.ext h
  have hv5 : s.val ≠ 5 := by
    intro h
    apply hne5
    have hacc : mulCheck.reject = (⟨5, by omega⟩ : Fin 6) := rfl
    rw [hacc]
    exact Fin.ext h
  simp only [mulMachine, mulEmbC]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [if_neg (by omega)]
  rw [dif_neg (by omega)]
  rw [dif_pos (by have := s.isLt; omega)]
  -- 内层状态 `18 + s.val - 18` 与 `s` 相等（仅数值层面不同）
  have hs : (⟨18 + s.val - 18, by omega⟩ : Fin 6) = s :=
    Fin.ext (by show 18 + s.val - 18 = s.val; omega)
  rw [hs]

/-- 整机在收尾机状态上照抄 `mulFinal`（除其接受态 3 外）。
    The whole machine mirrors `mulFinal` on final states except its accept state. -/
theorem mulMachine_step_final (s : Fin 4) (a : Sym) (hne : s ≠ mulFinal.accept) :
    mulMachine.step (mulEmbF s) a
      = (mulEmbF (mulFinal.step s a).1, (mulFinal.step s a).2) := by
  have hv : s.val ≠ 3 := by
    intro h
    apply hne
    have hacc : mulFinal.accept = (⟨3, by omega⟩ : Fin 4) := rfl
    rw [hacc]
    exact Fin.ext h
  simp only [mulMachine, mulEmbF]
  rw [if_neg (by have := s.isLt; omega)]
  rw [if_neg (by have := s.isLt; omega)]
  rw [if_neg (by have := s.isLt; omega)]
  rw [dif_neg (by have := s.isLt; omega)]
  rw [dif_neg (by have := s.isLt; omega)]
  -- 内层状态 `24 + s.val - 24` 与 `s` 相等（仅数值层面不同）
  have hs : (⟨24 + s.val - 24, by omega⟩ : Fin 4) = s :=
    Fin.ext (by show 24 + s.val - 24 = s.val; omega)
  rw [hs]

/-- 整机在「轮接受态 17」上的转移：进入检测入口（原地、纸带不变）。
    Redirect from the round's accept state to the check entry. -/
theorem mulMachine_step_17 (a : Sym) :
    mulMachine.step (mulEmbR mulRound.accept) a
      = ((⟨18, by omega⟩ : Fin 28), a, Dir.stay) := by
  have hv : mulRound.accept.val = 17 := rfl
  simp only [mulMachine, mulEmbR, Fin.val_castLE, hv]
  simp

/-- 整机在「检测继续态 22」上的转移：回到轮起点。
    Redirect from the check's continue state back to the round start. -/
theorem mulMachine_step_22 (a : Sym) :
    mulMachine.step (mulEmbC mulCheck.accept) a
      = ((⟨0, by omega⟩ : Fin 28), a, Dir.stay) := by
  have hv : mulCheck.accept.val = 4 := rfl
  simp only [mulMachine, mulEmbC, hv]
  simp

/-- 整机在「检测耗尽态 23」上的转移：进入收尾入口。
    Redirect from the check's exhausted state to the final entry. -/
theorem mulMachine_step_23 (a : Sym) :
    mulMachine.step (mulEmbC mulCheck.reject) a
      = ((⟨24, by omega⟩ : Fin 28), a, Dir.stay) := by
  have hv : mulCheck.reject.val = 5 := rfl
  simp only [mulMachine, mulEmbC, hv]
  simp

/-- 嵌入后的非终止状态在整机里也不终止（轮机侧）。 -/
theorem mulMachine_halt_round (s : Fin 18) :
    mulMachine.accept ≠ mulEmbR s ∧ mulMachine.reject ≠ mulEmbR s := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp only [mulMachine, mulEmbR, Fin.val_castLE] at hv
    have h3 := s.isLt
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [mulMachine, mulEmbR, Fin.val_castLE] at hv
    have h3 := s.isLt
    omega

/-- 嵌入后的非终止状态在整机里也不终止（检测机侧）。 -/
theorem mulMachine_halt_check (s : Fin 6) :
    mulMachine.accept ≠ mulEmbC s ∧ mulMachine.reject ≠ mulEmbC s := by
  constructor
  · intro h
    have hv := congrArg Fin.val h
    simp only [mulMachine, mulEmbC] at hv
    have h3 := s.isLt
    omega
  · intro h
    have hv := congrArg Fin.val h
    simp only [mulMachine, mulEmbC] at hv
    have h3 := s.isLt
    omega

/-- 嵌入后的非终止状态在整机里也不终止（收尾机侧，须避开其接受态）。 -/
theorem mulMachine_halt_final (s : Fin 4) (hne : s ≠ mulFinal.accept) :
    mulMachine.accept ≠ mulEmbF s ∧ mulMachine.reject ≠ mulEmbF s := by
  have hv : s.val ≠ 3 := by
    intro h
    apply hne
    have hacc : mulFinal.accept = (⟨3, by omega⟩ : Fin 4) := rfl
    rw [hacc]
    exact Fin.ext h
  constructor
  · intro h
    have hv' := congrArg Fin.val h
    simp only [mulMachine, mulEmbF] at hv'
    omega
  · intro h
    have hv' := congrArg Fin.val h
    simp only [mulMachine, mulEmbF] at hv'
    omega

/-- 整机照搬轮机的一段运行（轮机全程不停机）。
    Whole-machine runs mirror round runs. -/
theorem mulMachine_run_round (n : Nat) (c : Config 18)
    (hnh : ∀ k, k < n → mulRound.halted (mulRound.run k c) = false) :
    mulMachine.run n ⟨mulEmbR c.state, c.tape⟩ =
      ⟨mulEmbR (mulRound.run n c).state, (mulRound.run n c).tape⟩ :=
  run_embed mulRound mulMachine mulEmbR
    (fun s a ha _ => mulMachine_step_round s a ha)
    (fun s _ _ => mulMachine_halt_round s) n c hnh

/-- 整机照搬检测机的一段运行（检测机全程不停机）。 -/
theorem mulMachine_run_check (n : Nat) (c : Config 6)
    (hnh : ∀ k, k < n → mulCheck.halted (mulCheck.run k c) = false) :
    mulMachine.run n ⟨mulEmbC c.state, c.tape⟩ =
      ⟨mulEmbC (mulCheck.run n c).state, (mulCheck.run n c).tape⟩ :=
  run_embed mulCheck mulMachine mulEmbC
    (fun s a h4 h5 => mulMachine_step_check s a h4 h5)
    (fun s _ _ => mulMachine_halt_check s) n c hnh

/-- 整机照搬收尾机的一段运行（收尾机全程不停机）。 -/
theorem mulMachine_run_final (n : Nat) (c : Config 4)
    (hnh : ∀ k, k < n → mulFinal.halted (mulFinal.run k c) = false) :
    mulMachine.run n ⟨mulEmbF c.state, c.tape⟩ =
      ⟨mulEmbF (mulFinal.run n c).state, (mulFinal.run n c).tape⟩ :=
  run_embed mulFinal mulMachine mulEmbF
    (fun s a ha _ => mulMachine_step_final s a ha)
    (fun s h1 _ => mulMachine_halt_final s h1) n c hnh

/-! ### 三个相位机的「段内不停机」引理 -/

/-- 以数值比较给出「非终止」前提的按段不停机引理（便于收口）。
    A numeral-based variant of `no_halt_of_run_end`. -/
theorem no_halt_of_run_end_nat {q : Nat} (M : DTM q) (n : Nat) (c : Config q) (s : Fin q)
    (t : Tape) (h : M.run n c = ⟨s, t⟩) (ha : s.val ≠ M.accept.val) (hr : s.val ≠ M.reject.val) :
    ∀ k, k < n → M.halted (M.run k c) = false := by
  refine no_halt_of_run_end M n c s t h ?_ ?_
  · intro hh
    exact ha (congrArg Fin.val hh)
  · intro hh
    exact hr (congrArg Fin.val hh)


/-- `Fin 6` 上数值不为 4 的元素与 `mulCheck.accept` 的数值不同。 -/
theorem mulCheck_val_ne_acc {st : Nat} (hst : st < 6) (h : st ≠ 4) :
    (⟨st, hst⟩ : Fin 6).val ≠ mulCheck.accept.val := by
  intro hh
  have hv : st = 4 := by
    rw [show mulCheck.accept.val = 4 from rfl] at hh
    simpa using hh
  exact h hv

/-- `Fin 6` 上数值不为 5 的元素与 `mulCheck.reject` 的数值不同。 -/
theorem mulCheck_val_ne_rej {st : Nat} (hst : st < 6) (h : st ≠ 5) :
    (⟨st, hst⟩ : Fin 6).val ≠ mulCheck.reject.val := by
  intro hh
  have hv : st = 5 := by
    rw [show mulCheck.reject.val = 5 from rfl] at hh
    simpa using hh
  exact h hv

/-- `Fin 4` 上数值不为 3 的元素与 `mulFinal.accept` 的数值不同。 -/
theorem mulFinal_val_ne {st : Nat} (hst : st < 4) (h : st ≠ 3) :
    (⟨st, hst⟩ : Fin 4).val ≠ mulFinal.accept.val := by
  intro hh
  have hv : st = 3 := by
    rw [show mulFinal.accept.val = 3 from rfl] at hh
    simpa using hh
  exact h hv

/-- 检测「继续」通路在最后一步之前不停机。
    The check's continue path never halts before its final step. -/
theorem mulCheck_continue_no_halt (a : Nat) (ha : 1 ≤ a) (P R : List Sym) :
    ∀ k, k < 2 * a + 4 →
      mulCheck.halted
        (mulCheck.run k
          ⟨(⟨0, by omega⟩ : Fin 6),
            Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some true :: P)))
              (some true :: (none :: R))⟩) = false := by
  rcases a with _ | a'
  · omega
  simp only [Nat.add_sub_cancel]
  -- 各段的累计终点（与 `mulCheck_continue_run` 同一分解）
  have c1 : mulCheck.run a'
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate a' (some true) ++ (none :: (some true :: P)))
          (some true :: (none :: R))⟩
      = ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (none :: (some true :: P))
            (List.replicate a' (some true) ++ (some true :: (none :: R)))⟩ :=
    mulCheck_skipA a' (none :: (some true :: P)) (none :: R)
  have c2 : mulCheck.run (a' + 1)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate a' (some true) ++ (none :: (some true :: P)))
          (some true :: (none :: R))⟩
      = ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (some true :: P)
            (none :: (some true :: (List.replicate a' (some true) ++ (none :: R))))⟩ := by
    rw [DTM.run_add mulCheck a' 1, c1]
    rw [← cons_replicate_append (some true) a' (none :: R)]
    rw [estepMK 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega) (by omega)]
    etape
  have c3 : mulCheck.run (a' + 1 + 1)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate a' (some true) ++ (none :: (some true :: P)))
          (some true :: (none :: R))⟩
      = ⟨(⟨1, by omega⟩ : Fin 6),
          Tape.mk P
            (some true :: (none ::
              (some true :: (List.replicate a' (some true) ++ (none :: R)))))⟩ := by
    rw [DTM.run_add mulCheck (a' + 1) 1, c2]
    rw [estepMK 0 (by omega) none _ _ _ (by rfl) _ _ (by omega) (by omega)]
    etape
  have c4 : mulCheck.run (a' + 1 + 1 + 1)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate a' (some true) ++ (none :: (some true :: P)))
          (some true :: (none :: R))⟩
      = ⟨(⟨2, by omega⟩ : Fin 6),
          Tape.mk (some true :: P)
            (none :: (some true :: (List.replicate a' (some true) ++ (none :: R))))⟩ := by
    rw [DTM.run_add mulCheck (a' + 1 + 1) 1, c3]
    rw [estepMK 1 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega) (by omega)]
    etape
  have c5 : mulCheck.run (a' + 1 + 1 + 1 + 1)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate a' (some true) ++ (none :: (some true :: P)))
          (some true :: (none :: R))⟩
      = ⟨(⟨3, by omega⟩ : Fin 6),
          Tape.mk (none :: (some true :: P))
            (some true :: (List.replicate a' (some true) ++ (none :: R)))⟩ := by
    rw [DTM.run_add mulCheck (a' + 1 + 1 + 1) 1, c4]
    rw [estepMK 2 (by omega) none _ _ _ (by rfl) _ _ (by omega) (by omega)]
    etape
  have c6 : mulCheck.run (a' + 1)
      (mulCheck.run (a' + 1 + 1 + 1 + 1)
        ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (List.replicate a' (some true) ++ (none :: (some true :: P)))
            (some true :: (none :: R))⟩)
      = ⟨(⟨3, by omega⟩ : Fin 6),
          Tape.mk (List.replicate (a' + 1) (some true) ++ (none :: (some true :: P)))
            (none :: R)⟩ := by
    rw [c5]
    rw [cons_replicate_append (some true) a' (none :: R)]
    rw [replicate_succ_append a' (some true) (none :: R)]
    rw [mulCheck_skipR (a' + 1) (none :: (some true :: P)) R]
  -- 各段不停机（起点状态从累计终点读出）
  have h1 : ∀ k, k < a' → mulCheck.halted
      (mulCheck.run k
        ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (List.replicate a' (some true) ++ (none :: (some true :: P)))
            (some true :: (none :: R))⟩) = false :=
    no_halt_of_run_end_nat mulCheck a' _ (⟨0, by omega⟩ : Fin 6) _ c1
      (mulCheck_val_ne_acc (by omega) (by decide)) (mulCheck_val_ne_rej (by omega) (by decide))
  have h2 : ∀ k, k < 1 → mulCheck.halted
      (mulCheck.run k (mulCheck.run a'
        ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (List.replicate a' (some true) ++ (none :: (some true :: P)))
            (some true :: (none :: R))⟩)) = false := by
    refine no_halt_one mulCheck _ ?_
    rw [c1]
    exact mulCheck_halted_ne 0 (by omega) (by decide) (by decide) _
  have h3 : ∀ k, k < 1 → mulCheck.halted
      (mulCheck.run k (mulCheck.run (a' + 1)
        ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (List.replicate a' (some true) ++ (none :: (some true :: P)))
            (some true :: (none :: R))⟩)) = false := by
    refine no_halt_one mulCheck _ ?_
    rw [c2]
    exact mulCheck_halted_ne 0 (by omega) (by decide) (by decide) _
  have h4 : ∀ k, k < 1 → mulCheck.halted
      (mulCheck.run k (mulCheck.run (a' + 1 + 1)
        ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (List.replicate a' (some true) ++ (none :: (some true :: P)))
            (some true :: (none :: R))⟩)) = false := by
    refine no_halt_one mulCheck _ ?_
    rw [c3]
    exact mulCheck_halted_ne 1 (by omega) (by decide) (by decide) _
  have h5 : ∀ k, k < 1 → mulCheck.halted
      (mulCheck.run k (mulCheck.run (a' + 1 + 1 + 1)
        ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (List.replicate a' (some true) ++ (none :: (some true :: P)))
            (some true :: (none :: R))⟩)) = false := by
    refine no_halt_one mulCheck _ ?_
    rw [c4]
    exact mulCheck_halted_ne 2 (by omega) (by decide) (by decide) _
  have h6 : ∀ k, k < a' + 1 → mulCheck.halted
      (mulCheck.run k (mulCheck.run (a' + 1 + 1 + 1 + 1)
        ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (List.replicate a' (some true) ++ (none :: (some true :: P)))
            (some true :: (none :: R))⟩)) = false :=
    no_halt_of_run_end_nat mulCheck (a' + 1) _ (⟨3, by omega⟩ : Fin 6) _ c6
      (mulCheck_val_ne_acc (by omega) (by decide)) (mulCheck_val_ne_rej (by omega) (by decide))
  have h7 : ∀ k, k < 1 → mulCheck.halted
      (mulCheck.run k (mulCheck.run (a' + 1 + 1 + 1 + 1 + (a' + 1))
        ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (List.replicate a' (some true) ++ (none :: (some true :: P)))
            (some true :: (none :: R))⟩)) = false := by
    refine no_halt_one mulCheck _ ?_
    rw [DTM.run_add mulCheck (a' + 1 + 1 + 1 + 1) (a' + 1)]
    rw [c6]
    exact mulCheck_halted_ne 3 (by omega) (by decide) (by decide) _
  -- 逐段拼接
  have hAB := no_halt_add mulCheck a' 1 _ h1 h2
  have hABC := no_halt_add mulCheck (a' + 1) 1 _ hAB h3
  have hABCD := no_halt_add mulCheck (a' + 1 + 1) 1 _ hABC h4
  have hABCDE := no_halt_add mulCheck (a' + 1 + 1 + 1) 1 _ hABCD h5
  have hABCDEF := no_halt_add mulCheck (a' + 1 + 1 + 1 + 1) (a' + 1) _ hABCDE h6
  have hAll := no_halt_add mulCheck (a' + 1 + 1 + 1 + 1 + (a' + 1)) 1 _ hABCDEF h7
  rw [show 2 * (a' + 1) + 4 = (a' + 1 + 1 + 1 + 1 + (a' + 1)) + 1 from by omega]
  exact hAll

/-- 检测「耗尽」通路在最后一步之前不停机。
    The check's exhausted path never halts before its final step. -/
theorem mulCheck_done_no_halt (a : Nat) (ha : 1 ≤ a) (P R : List Sym) :
    ∀ k, k < a + 2 →
      mulCheck.halted
        (mulCheck.run k
          ⟨(⟨0, by omega⟩ : Fin 6),
            Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some false :: P)))
              (some true :: (none :: R))⟩) = false := by
  rcases a with _ | a'
  · omega
  simp only [Nat.add_sub_cancel]
  have c1 : mulCheck.run a'
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate a' (some true) ++ (none :: (some false :: P)))
          (some true :: (none :: R))⟩
      = ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (none :: (some false :: P))
            (List.replicate a' (some true) ++ (some true :: (none :: R)))⟩ :=
    mulCheck_skipA a' (none :: (some false :: P)) (none :: R)
  have c2 : mulCheck.run (a' + 1)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate a' (some true) ++ (none :: (some false :: P)))
          (some true :: (none :: R))⟩
      = ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (some false :: P)
            (none :: (some true :: (List.replicate a' (some true) ++ (none :: R))))⟩ := by
    rw [DTM.run_add mulCheck a' 1, c1]
    rw [← cons_replicate_append (some true) a' (none :: R)]
    rw [estepMK 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega) (by omega)]
    etape
  have c3 : mulCheck.run (a' + 1 + 1)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate a' (some true) ++ (none :: (some false :: P)))
          (some true :: (none :: R))⟩
      = ⟨(⟨1, by omega⟩ : Fin 6),
          Tape.mk P
            (some false :: (none ::
              (some true :: (List.replicate a' (some true) ++ (none :: R)))))⟩ := by
    rw [DTM.run_add mulCheck (a' + 1) 1, c2]
    rw [estepMK 0 (by omega) none _ _ _ (by rfl) _ _ (by omega) (by omega)]
    etape
  have h1 : ∀ k, k < a' → mulCheck.halted
      (mulCheck.run k
        ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (List.replicate a' (some true) ++ (none :: (some false :: P)))
            (some true :: (none :: R))⟩) = false :=
    no_halt_of_run_end_nat mulCheck a' _ (⟨0, by omega⟩ : Fin 6) _ c1
      (mulCheck_val_ne_acc (by omega) (by decide)) (mulCheck_val_ne_rej (by omega) (by decide))
  have h2 : ∀ k, k < 1 → mulCheck.halted
      (mulCheck.run k (mulCheck.run a'
        ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (List.replicate a' (some true) ++ (none :: (some false :: P)))
            (some true :: (none :: R))⟩)) = false := by
    refine no_halt_one mulCheck _ ?_
    rw [c1]
    exact mulCheck_halted_ne 0 (by omega) (by decide) (by decide) _
  have h3 : ∀ k, k < 1 → mulCheck.halted
      (mulCheck.run k (mulCheck.run (a' + 1)
        ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (List.replicate a' (some true) ++ (none :: (some false :: P)))
            (some true :: (none :: R))⟩)) = false := by
    refine no_halt_one mulCheck _ ?_
    rw [c2]
    exact mulCheck_halted_ne 0 (by omega) (by decide) (by decide) _
  have h4 : ∀ k, k < 1 → mulCheck.halted
      (mulCheck.run k (mulCheck.run (a' + 1 + 1)
        ⟨(⟨0, by omega⟩ : Fin 6),
          Tape.mk (List.replicate a' (some true) ++ (none :: (some false :: P)))
            (some true :: (none :: R))⟩)) = false := by
    refine no_halt_one mulCheck _ ?_
    rw [c3]
    exact mulCheck_halted_ne 1 (by omega) (by decide) (by decide) _
  have hAB := no_halt_add mulCheck a' 1 _ h1 h2
  have hABC := no_halt_add mulCheck (a' + 1) 1 _ hAB h3
  have hAll := no_halt_add mulCheck (a' + 1 + 1) 1 _ hABC h4
  rw [show a' + 1 + 2 = (a' + 1 + 1) + 1 from by omega]
  exact hAll

/-- 收尾相位在最后一步之前不停机。
    The final phase never halts before its final step. -/
theorem mulFinal_no_halt (a d : Nat) (ha : 1 ≤ a) (hd : 1 ≤ d) (P R : List Sym) :
    ∀ k, k < a + d + 4 →
      mulFinal.halted
        (mulFinal.run k
          ⟨(⟨0, by omega⟩ : Fin 4),
            Tape.mk P (some false :: (none ::
              (List.replicate (a - 1) (some true) ++
                (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩) = false := by
  rcases a with _ | a'
  · omega
  simp only [Nat.add_sub_cancel]
  have f1 : mulFinal.run 1
      ⟨(⟨0, by omega⟩ : Fin 4),
        Tape.mk P (some false :: (none ::
          (List.replicate a' (some true) ++
            (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩
      = ⟨(⟨0, by omega⟩ : Fin 4),
          Tape.mk (some false :: P) (none ::
            (List.replicate a' (some true) ++
              (some true :: (none :: (List.replicate d (some false) ++ (none :: R))))))⟩ := by
    rw [estepMF2 0 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
    etape
  have f2 : mulFinal.run (1 + 1)
      ⟨(⟨0, by omega⟩ : Fin 4),
        Tape.mk P (some false :: (none ::
          (List.replicate a' (some true) ++
            (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩
      = ⟨(⟨1, by omega⟩ : Fin 4),
          Tape.mk (none :: (some false :: P))
            (List.replicate a' (some true) ++
              (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))⟩ := by
    rw [DTM.run_add mulFinal 1 1, f1]
    rw [estepMF2 0 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
    etape
  have f3 : mulFinal.run (a' + 1) (mulFinal.run (1 + 1)
      ⟨(⟨0, by omega⟩ : Fin 4),
        Tape.mk P (some false :: (none ::
          (List.replicate a' (some true) ++
            (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩)
      = ⟨(⟨1, by omega⟩ : Fin 4),
          Tape.mk (List.replicate (a' + 1) (some true) ++ (none :: (some false :: P)))
            (none :: (List.replicate d (some false) ++ (none :: R)))⟩ := by
    rw [f2]
    rw [replicate_succ_append a' (some true)
      (none :: (List.replicate d (some false) ++ (none :: R)))]
    rw [mulFinal_skipT (a' + 1) (none :: (some false :: P))
      (List.replicate d (some false) ++ (none :: R))]
  have f4 : mulFinal.run 1 (mulFinal.run (a' + 1) (mulFinal.run (1 + 1)
      ⟨(⟨0, by omega⟩ : Fin 4),
        Tape.mk P (some false :: (none ::
          (List.replicate a' (some true) ++
            (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩))
      = ⟨(⟨2, by omega⟩ : Fin 4),
          Tape.mk (none :: (List.replicate (a' + 1) (some true) ++ (none :: (some false :: P))))
            (List.replicate d (some false) ++ (none :: R))⟩ := by
    rw [f3]
    rw [estepMF2 1 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
    etape
  have f5 : mulFinal.run d (mulFinal.run 1 (mulFinal.run (a' + 1) (mulFinal.run (1 + 1)
      ⟨(⟨0, by omega⟩ : Fin 4),
        Tape.mk P (some false :: (none ::
          (List.replicate a' (some true) ++
            (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩)))
      = ⟨(⟨2, by omega⟩ : Fin 4),
          Tape.mk (List.replicate d (some true) ++
              (none :: (List.replicate (a' + 1) (some true) ++ (none :: (some false :: P)))))
            (none :: R)⟩ := by
    rw [f4]
    rw [mulFinal_conv d
      (none :: (List.replicate (a' + 1) (some true) ++ (none :: (some false :: P)))) R]
  -- 各段不停机
  have g1 : ∀ k, k < 1 → mulFinal.halted
      (mulFinal.run k
        ⟨(⟨0, by omega⟩ : Fin 4),
          Tape.mk P (some false :: (none ::
            (List.replicate a' (some true) ++
              (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩) = false := by
    refine no_halt_one mulFinal _ ?_
    exact mulFinal_halted_ne 0 (by omega) (by decide) _
  have g2 : ∀ k, k < 1 → mulFinal.halted
      (mulFinal.run k (mulFinal.run 1
        ⟨(⟨0, by omega⟩ : Fin 4),
          Tape.mk P (some false :: (none ::
            (List.replicate a' (some true) ++
              (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩)) = false := by
    refine no_halt_one mulFinal _ ?_
    rw [f1]
    exact mulFinal_halted_ne 0 (by omega) (by decide) _
  have g3 : ∀ k, k < a' + 1 → mulFinal.halted
      (mulFinal.run k (mulFinal.run (1 + 1)
        ⟨(⟨0, by omega⟩ : Fin 4),
          Tape.mk P (some false :: (none ::
            (List.replicate a' (some true) ++
              (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩)) = false :=
    no_halt_of_run_end_nat mulFinal (a' + 1) _ (⟨1, by omega⟩ : Fin 4) _ f3
      (mulFinal_val_ne (by omega) (by decide)) (mulFinal_val_ne (by omega) (by decide))
  have f4c : mulFinal.run 1 (mulFinal.run (1 + 1 + (a' + 1))
      ⟨(⟨0, by omega⟩ : Fin 4),
        Tape.mk P (some false :: (none ::
          (List.replicate a' (some true) ++
            (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩)
      = ⟨(⟨2, by omega⟩ : Fin 4),
          Tape.mk (none :: (List.replicate (a' + 1) (some true) ++ (none :: (some false :: P))))
            (List.replicate d (some false) ++ (none :: R))⟩ := by
    rw [DTM.run_add mulFinal (1 + 1) (a' + 1)]
    rw [f4]
  have g4 : ∀ k, k < 1 → mulFinal.halted
      (mulFinal.run k (mulFinal.run (1 + 1 + (a' + 1))
        ⟨(⟨0, by omega⟩ : Fin 4),
          Tape.mk P (some false :: (none ::
            (List.replicate a' (some true) ++
              (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩)) = false :=
    no_halt_of_run_end_nat mulFinal 1 _ (⟨2, by omega⟩ : Fin 4) _ f4c
      (mulFinal_val_ne (by omega) (by decide)) (mulFinal_val_ne (by omega) (by decide))
  have f5c : mulFinal.run d (mulFinal.run (1 + 1 + (a' + 1) + 1)
      ⟨(⟨0, by omega⟩ : Fin 4),
        Tape.mk P (some false :: (none ::
          (List.replicate a' (some true) ++
            (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩)
      = ⟨(⟨2, by omega⟩ : Fin 4),
          Tape.mk (List.replicate d (some true) ++
              (none :: (List.replicate (a' + 1) (some true) ++ (none :: (some false :: P)))))
            (none :: R)⟩ := by
    rw [DTM.run_add mulFinal (1 + 1 + (a' + 1)) 1]
    rw [DTM.run_add mulFinal (1 + 1) (a' + 1)]
    rw [f5]
  have g5 : ∀ k, k < d → mulFinal.halted
      (mulFinal.run k (mulFinal.run (1 + 1 + (a' + 1) + 1)
        ⟨(⟨0, by omega⟩ : Fin 4),
          Tape.mk P (some false :: (none ::
            (List.replicate a' (some true) ++
              (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩)) = false :=
    no_halt_of_run_end_nat mulFinal d _ (⟨2, by omega⟩ : Fin 4) _ f5c
      (mulFinal_val_ne (by omega) (by decide)) (mulFinal_val_ne (by omega) (by decide))
  have g6 : ∀ k, k < 1 → mulFinal.halted
      (mulFinal.run k (mulFinal.run (1 + 1 + (a' + 1) + 1 + d)
        ⟨(⟨0, by omega⟩ : Fin 4),
          Tape.mk P (some false :: (none ::
            (List.replicate a' (some true) ++
              (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩)) = false := by
    refine no_halt_one mulFinal _ ?_
    rw [DTM.run_add mulFinal (1 + 1 + (a' + 1) + 1) d]
    rw [f5c]
    exact mulFinal_halted_ne 2 (by omega) (by decide) _
  have gA := no_halt_add mulFinal 1 1 _ g1 g2
  have gB := no_halt_add mulFinal (1 + 1) (a' + 1) _ gA g3
  have gC := no_halt_add mulFinal (1 + 1 + (a' + 1)) 1 _ gB g4
  have gD := no_halt_add mulFinal (1 + 1 + (a' + 1) + 1) d _ gC g5
  have gAll := no_halt_add mulFinal (1 + 1 + (a' + 1) + 1 + d) 1 _ gD g6
  rw [show a' + 1 + d + 4 = (1 + 1 + (a' + 1) + 1 + d) + 1 from by omega]
  exact gAll

/-! ### 整机阶段搬运（轮 / 检测 / 收尾） -/

/-- 整机在给定格局的停机判定（便于用状态不等式收口）。 -/
theorem mulMachine_halted_false (s : Fin 28) (t : Tape)
    (h1 : s ≠ mulMachine.accept) (h2 : s ≠ mulMachine.reject) :
    mulMachine.halted ⟨s, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  exact ⟨beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2⟩

/-- 整机**一轮**：轮机的整段运行 + 1 步改接（接受态 17 → 检测入口 18）。
    One whole-machine round: the round's run plus the redirect step 17 → 18. -/
theorem mulMachine_phase_round (a b r w d : Nat) (ha : 1 ≤ a) (hb : 1 ≤ b - r) (hwa : a ≤ w)
    (L R : List Sym) :
    mulMachine.run (mulRoundSteps a b r w d + 1)
      ⟨mulMachine.start, Tape.mk (mulL a b r 0 L) (mulR d 0 w R)⟩
      = ⟨mulEmbC mulCheck.start,
          Tape.mk (mulL a b (r + 1) 0 L) (mulR (d + a) 0 (w - a) R)⟩ := by
  show mulMachine.run (mulRoundSteps a b r w d + 1)
      ⟨mulEmbR mulRound.start, Tape.mk (mulL a b r 0 L) (mulR d 0 w R)⟩
      = ⟨mulEmbC mulCheck.start,
          Tape.mk (mulL a b (r + 1) 0 L) (mulR (d + a) 0 (w - a) R)⟩
  have h1 := mulMachine_run_round (mulRoundSteps a b r w d)
    ⟨mulRound.start, Tape.mk (mulL a b r 0 L) (mulR d 0 w R)⟩
    (mulRound_no_halt a b r w d ha hb hwa L R)
  have h2 : mulRound.run (mulRoundSteps a b r w d)
      ⟨mulRound.start, Tape.mk (mulL a b r 0 L) (mulR d 0 w R)⟩
      = ⟨mulRound.accept,
          Tape.mk (mulL a b (r + 1) 0 L) (mulR (d + a) 0 (w - a) R)⟩ :=
    mulRound_run a b r w d ha hb hwa L R
  rw [h2] at h1
  dsimp only at h1
  have hnh : mulMachine.halted
      ⟨mulEmbR mulRound.accept,
        Tape.mk (mulL a b (r + 1) 0 L) (mulR (d + a) 0 (w - a) R)⟩ = false := by
    have hh := mulMachine_halt_round mulRound.accept
    exact mulMachine_halted_false _ _ hh.1.symm hh.2.symm
  have hstep : mulMachine.stepConfig
      ⟨mulEmbR mulRound.accept,
        Tape.mk (mulL a b (r + 1) 0 L) (mulR (d + a) 0 (w - a) R)⟩ =
      ⟨mulEmbC mulCheck.start,
        Tape.mk (mulL a b (r + 1) 0 L) (mulR (d + a) 0 (w - a) R)⟩ := by
    rw [DTM.stepConfig, mulMachine_step_17]
    simp [Tape.write_read, Tape.move, mulEmbC, mulCheck]
  rw [DTM.run_add mulMachine (mulRoundSteps a b r w d) 1, h1]
  rw [DTM.run_succ_of_not_halted mulMachine 0 _ hnh]
  exact hstep

/-- 检测「继续」：检测段 + 1 步改接（22 → 0），把机器带回轮的起点。
    Check (continue): the check segment plus the redirect step 22 → 0. -/
theorem mulMachine_phase_check_continue (a : Nat) (ha : 1 ≤ a) (P R : List Sym) :
    mulMachine.run (2 * a + 4 + 1)
      ⟨mulEmbC mulCheck.start,
        Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some true :: P)))
          (some true :: (none :: R))⟩
      = ⟨(⟨0, by omega⟩ : Fin 28),
          Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some true :: P)))
            (some true :: (none :: R))⟩ := by
  show mulMachine.run (2 * a + 4 + 1)
      ⟨mulEmbC (⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some true :: P)))
          (some true :: (none :: R))⟩
      = ⟨(⟨0, by omega⟩ : Fin 28),
          Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some true :: P)))
            (some true :: (none :: R))⟩
  have h1 := mulMachine_run_check (2 * a + 4)
    ⟨(⟨0, by omega⟩ : Fin 6),
      Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some true :: P)))
        (some true :: (none :: R))⟩
    (mulCheck_continue_no_halt a ha P R)
  have h2 : mulCheck.run (2 * a + 4)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some true :: P)))
          (some true :: (none :: R))⟩
      = ⟨mulCheck.accept,
          Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some true :: P)))
            (some true :: (none :: R))⟩ := by
    simpa [mulCheck] using mulCheck_continue_run a ha P R
  rw [h2] at h1
  dsimp only at h1
  have hnh : mulMachine.halted
      ⟨mulEmbC mulCheck.accept,
        Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some true :: P)))
          (some true :: (none :: R))⟩ = false := by
    have hh := mulMachine_halt_check mulCheck.accept
    exact mulMachine_halted_false _ _ hh.1.symm hh.2.symm
  have hstep : mulMachine.stepConfig
      ⟨mulEmbC mulCheck.accept,
        Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some true :: P)))
          (some true :: (none :: R))⟩ =
      ⟨(⟨0, by omega⟩ : Fin 28),
        Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some true :: P)))
          (some true :: (none :: R))⟩ := by
    rw [DTM.stepConfig, mulMachine_step_22]
    simp [Tape.write_read, Tape.move]
  rw [DTM.run_add mulMachine (2 * a + 4) 1, h1]
  rw [DTM.run_succ_of_not_halted mulMachine 0 _ hnh]
  exact hstep

/-- 检测「耗尽」：检测段 + 1 步改接（23 → 24），进入收尾相位。
    Check (exhausted): the check segment plus the redirect step 23 → 24. -/
theorem mulMachine_phase_check_done (a : Nat) (ha : 1 ≤ a) (P R : List Sym) :
    mulMachine.run (a + 2 + 1)
      ⟨mulEmbC mulCheck.start,
        Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some false :: P)))
          (some true :: (none :: R))⟩
      = ⟨mulEmbF mulFinal.start,
          Tape.mk P (some false :: (none ::
            (List.replicate (a - 1) (some true) ++ (some true :: (none :: R)))))⟩ := by
  show mulMachine.run (a + 2 + 1)
      ⟨mulEmbC (⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some false :: P)))
          (some true :: (none :: R))⟩
      = ⟨mulEmbF (⟨0, by omega⟩ : Fin 4),
          Tape.mk P (some false :: (none ::
            (List.replicate (a - 1) (some true) ++ (some true :: (none :: R)))))⟩
  have h1 := mulMachine_run_check (a + 2)
    ⟨(⟨0, by omega⟩ : Fin 6),
      Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some false :: P)))
        (some true :: (none :: R))⟩
    (mulCheck_done_no_halt a ha P R)
  have h2 : mulCheck.run (a + 2)
      ⟨(⟨0, by omega⟩ : Fin 6),
        Tape.mk (List.replicate (a - 1) (some true) ++ (none :: (some false :: P)))
          (some true :: (none :: R))⟩
      = ⟨mulCheck.reject,
          Tape.mk P (some false :: (none ::
            (List.replicate (a - 1) (some true) ++ (some true :: (none :: R)))))⟩ := by
    simpa [mulCheck] using mulCheck_done_run a ha P R
  rw [h2] at h1
  dsimp only at h1
  have hnh : mulMachine.halted
      ⟨mulEmbC mulCheck.reject,
        Tape.mk P (some false :: (none ::
          (List.replicate (a - 1) (some true) ++ (some true :: (none :: R)))))⟩ = false := by
    have hh := mulMachine_halt_check mulCheck.reject
    exact mulMachine_halted_false _ _ hh.1.symm hh.2.symm
  have hstep : mulMachine.stepConfig
      ⟨mulEmbC mulCheck.reject,
        Tape.mk P (some false :: (none ::
          (List.replicate (a - 1) (some true) ++ (some true :: (none :: R)))))⟩ =
      ⟨mulEmbF mulFinal.start,
        Tape.mk P (some false :: (none ::
          (List.replicate (a - 1) (some true) ++ (some true :: (none :: R)))))⟩ := by
    rw [DTM.stepConfig, mulMachine_step_23]
    simp [Tape.write_read, Tape.move, mulEmbF, mulFinal]
  rw [DTM.run_add mulMachine (a + 2) 1, h1]
  rw [DTM.run_succ_of_not_halted mulMachine 0 _ hnh]
  exact hstep

/-- 收尾相位：从 B 的耗尽位置跑到接受态（27）。
    The final phase: from B's exhausted position all the way to the accept state. -/
theorem mulMachine_phase_final (a d : Nat) (ha : 1 ≤ a) (hd : 1 ≤ d) (P R : List Sym) :
    mulMachine.run (a + d + 4)
      ⟨mulEmbF mulFinal.start,
        Tape.mk P (some false :: (none ::
          (List.replicate (a - 1) (some true) ++
            (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩
      = ⟨mulEmbF mulFinal.accept,
          Tape.mk (List.replicate d (some true) ++
              (none :: (List.replicate a (some true) ++ (none :: (some false :: P)))))
            (none :: R)⟩ := by
  show mulMachine.run (a + d + 4)
      ⟨mulEmbF (⟨0, by omega⟩ : Fin 4),
        Tape.mk P (some false :: (none ::
          (List.replicate (a - 1) (some true) ++
            (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩
      = ⟨mulEmbF mulFinal.accept,
          Tape.mk (List.replicate d (some true) ++
              (none :: (List.replicate a (some true) ++ (none :: (some false :: P)))))
            (none :: R)⟩
  have h1 := mulMachine_run_final (a + d + 4)
    ⟨(⟨0, by omega⟩ : Fin 4),
      Tape.mk P (some false :: (none ::
        (List.replicate (a - 1) (some true) ++
          (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩
    (mulFinal_no_halt a d ha hd P R)
  have h2 : mulFinal.run (a + d + 4)
      ⟨(⟨0, by omega⟩ : Fin 4),
        Tape.mk P (some false :: (none ::
          (List.replicate (a - 1) (some true) ++
            (some true :: (none :: (List.replicate d (some false) ++ (none :: R)))))))⟩
      = ⟨mulFinal.accept,
          Tape.mk (List.replicate d (some true) ++
              (none :: (List.replicate a (some true) ++ (none :: (some false :: P)))))
            (none :: R)⟩ := by
    simpa [mulFinal] using mulFinal_run a d ha hd P R
  rw [h2] at h1
  dsimp only at h1
  simpa using h1


/-- `mulMachine.start` 的字面量形态。 -/
theorem mulMachine_start_eq : mulMachine.start = (⟨0, by omega⟩ : Fin 28) := rfl

/-! ### 循环步与多轮不变式 -/

/-- 「一轮 + 检测继续」的整机运行：回到轮起点，`r ↦ r+1`、`d ↦ d+a`、`w ↦ w-a`。
    The "round + continue check" whole-machine step returns to the round start. -/
theorem mulMachine_loop_step (a b r w d : Nat) (ha : 1 ≤ a) (hb : r + 2 ≤ b) (hwa : a ≤ w)
    (L R : List Sym) :
    mulMachine.run (mulRoundSteps a b r w d + 1 + (2 * a + 4) + 1)
      ⟨mulMachine.start, Tape.mk (mulL a b r 0 L) (mulR d 0 w R)⟩
      = ⟨mulMachine.start, Tape.mk (mulL a b (r + 1) 0 L) (mulR (d + a) 0 (w - a) R)⟩ := by
  -- B 还剩 `k+1` 个未消费格 ⇒ 检测读到 `some true`
  have hb1 : 1 ≤ b - (r + 1) := by omega
  rcases hb' : b - (r + 1) with _ | k
  · omega
  have hshape : mulB b (r + 1) L
      = none :: (some true :: (List.replicate k (some true) ++
          (List.replicate (r + 1) (some false) ++ (none :: (none :: L))))) := by
    simp only [mulB]
    rw [hb', List.replicate_succ]
    simp
  have hP : mulL a b (r + 1) 0 L
      = List.replicate (a - 1) (some true) ++ (none :: (some true ::
          (List.replicate k (some true) ++
            (List.replicate (r + 1) (some false) ++ (none :: (none :: L)))))) := by
    simp only [mulL, Nat.sub_zero]
    rw [hshape]
  have hQ : mulR (d + a) 0 (w - a) R
      = some true :: (none :: (List.replicate (d + a) (some false) ++
          (none :: (List.replicate (w - a) (none : Sym) ++ R)))) := by
    simp [mulR]
  rw [show mulRoundSteps a b r w d + 1 + (2 * a + 4) + 1
      = (mulRoundSteps a b r w d + 1) + (2 * a + 4 + 1) from by omega]
  rw [DTM.run_add mulMachine (mulRoundSteps a b r w d + 1) (2 * a + 4 + 1)]
  rw [mulMachine_phase_round a b r w d ha (by omega) hwa L R]
  rw [hP, hQ]
  rw [mulMachine_phase_check_continue a ha
    (List.replicate k (some true) ++
      (List.replicate (r + 1) (some false) ++ (none :: (none :: L))))
    (List.replicate (d + a) (some false) ++
      (none :: (List.replicate (w - a) (none : Sym) ++ R)))]
  rw [← hP, ← hQ]
  rw [← mulMachine_start_eq]

/-- 到第 `k` 轮为止的累计步数。
    Total steps up to (and including) round `k` and its continue checks. -/
def mulLoopSteps : Nat → Nat → Nat → Nat → Nat
  | 0, _, _, _ => 0
  | k + 1, a, b, W =>
      mulLoopSteps k a b W + (mulRoundSteps a b k (W - k * a) (k * a) + 1 + (2 * a + 4) + 1)

/-- **多轮循环不变式**：从 `r = 0, d = 0, w = W` 出发，前 `k` 轮（每轮后接继续检测）
    让机器回到轮起点，且 `r = k`、`d = k·a`、`w = W - k·a`。
    The multi-round invariant: `k` rounds (each followed by a continue check) bring the
    machine back to the round start with `r = k`, `d = k·a`, `w = W - k·a`. -/
theorem mulMachine_loops : ∀ (k a b W : Nat), 1 ≤ a → k + 2 ≤ b → k * a ≤ W →
    ∀ L R : List Sym,
    mulMachine.run (mulLoopSteps k a b W)
      ⟨mulMachine.start, Tape.mk (mulL a b 0 0 L) (mulR 0 0 W R)⟩
      = ⟨mulMachine.start, Tape.mk (mulL a b k 0 L) (mulR (k * a) 0 (W - k * a) R)⟩ := by
  intro k
  induction k with
  | zero =>
      intro a b W _ _ _ L R
      simp [mulLoopSteps, DTM.run]
  | succ k ih =>
      intro a b W ha hk hW L R
      rw [show mulLoopSteps (k + 1) a b W
          = mulLoopSteps k a b W
            + (mulRoundSteps a b k (W - k * a) (k * a) + 1 + (2 * a + 4) + 1) from rfl]
      rw [DTM.run_add]
      have hk' : k + 2 ≤ b := by omega
      have hW' : k * a ≤ W := by
        have h := hW
        rw [Nat.succ_mul] at h
        omega
      have hwa' : a ≤ W - k * a := by
        have h := hW
        rw [Nat.succ_mul] at h
        omega
      rw [ih a b W ha hk' hW' L R]
      rw [mulMachine_loop_step a b k (W - k * a) (k * a) ha hk' hwa' L R]
      rw [Nat.succ_mul]
      rw [show W - k * a - a = W - (k * a + a) from by omega]

/-- `b·a = (b-1)·a + a`（`b ≥ 1`）。
    `b·a = (b-1)·a + a` for `b ≥ 1`. -/
theorem mul_eq_pred_mul_add (a b : Nat) (h : 1 ≤ b) : b * a = (b - 1) * a + a := by
  match b with
  | 0 => omega
  | k + 1 =>
    show (k + 1) * a = ((k + 1) - 1) * a + a
    rw [Nat.succ_mul]
    simp

/-- `(b-1)·a = (b-2)·a + a`（`b ≥ 2`）。
    `(b-1)·a = (b-2)·a + a` for `b ≥ 2`. -/
theorem pred_mul_eq (a b : Nat) (h : 2 ≤ b) : (b - 1) * a = (b - 2) * a + a := by
  match b with
  | 0 => omega
  | 1 => omega
  | k + 2 =>
    show ((k + 2) - 1) * a = ((k + 2) - 2) * a + a
    rw [show (k + 2) - 1 = k + 1 from by omega,
      show (k + 2) - 2 = k from by omega, Nat.succ_mul]

/-! ### 整机主定理：`b` 轮乘法（自动收尾） -/

/-- **乘法整机主定理**：从 `r = 0, d = 0, w = W` 出发，整机自动跑 `b` 轮（前 `b-2` 轮
    后接「继续」检测、第 `b-1` 轮后接「耗尽」检测），再做收尾相位，停在接受态；
    副本区得到 `b·a` 个 `some true`。
    The whole multiplication machine: `b` automatic rounds (followed by continue checks except
    the last, which is followed by the exhaustion check), then the final phase; it halts in the
    accept state with `b·a` copies. -/
theorem mulMachine_finish_run (a b W : Nat) (ha : 1 ≤ a) (hb : 2 ≤ b) (hW : b * a ≤ W)
    (L R : List Sym) :
    mulMachine.run
      (mulLoopSteps (b - 2) a b W
        + (mulRoundSteps a b (b - 2) (W - (b - 2) * a) ((b - 2) * a) + 1 + (2 * a + 4) + 1)
        + (mulRoundSteps a b (b - 1) (W - (b - 1) * a) ((b - 1) * a) + 1)
        + (a + 2 + 1)
        + (a + b * a + 4))
      ⟨mulMachine.start, Tape.mk (mulL a b 0 0 L) (mulR 0 0 W R)⟩
      = ⟨mulEmbF mulFinal.accept,
          Tape.mk (List.replicate (b * a) (some true) ++
              (none :: (List.replicate a (some true) ++
                (none :: (some false ::
                  (List.replicate (b - 1) (some false) ++ (none :: (none :: L))))))))
            (none :: (List.replicate (W - b * a) (none : Sym) ++ R))⟩ := by
  -- 循环段
  have hW2 : (b - 2) * a ≤ W :=
    Nat.le_trans (Nat.mul_le_mul_right a (by omega : b - 2 ≤ b)) hW
  have hloop := mulMachine_loops (b - 2) a b W ha (by omega) hW2 L R
  -- 各桥接等式
  have hmulb : b * a = (b - 1) * a + a := mul_eq_pred_mul_add a b (by omega)
  have hmulb2 : (b - 1) * a = (b - 2) * a + a := pred_mul_eq a b (by omega)
  have hb1 : a ≤ W - (b - 1) * a := by
    have h := hW
    rw [hmulb] at h
    omega
  have hwa2 : a ≤ W - (b - 2) * a := by
    have h1 : (b - 2) * a + a ≤ W := by
      have h := hW
      rw [hmulb, hmulb2] at h
      omega
    omega
  -- 最后一轮后的形态：B 已耗尽（首格 `some false`）
  have hP2 : mulL a b b 0 L
      = List.replicate (a - 1) (some true) ++ (none :: (some false ::
          (List.replicate (b - 1) (some false) ++ (none :: (none :: L))))) := by
    simp only [mulL, mulB, Nat.sub_zero]
    rw [show b - b = 0 from by omega]
    rw [show b = b - 1 + 1 from by omega, List.replicate_succ]
    simp
  have hQ2 : mulR (b * a) 0 (W - b * a) R
      = some true :: (none :: (List.replicate (b * a) (some false) ++
          (none :: (List.replicate (W - b * a) (none : Sym) ++ R)))) := by
    simp [mulR]
  -- 步数分解
  rw [show mulLoopSteps (b - 2) a b W
        + (mulRoundSteps a b (b - 2) (W - (b - 2) * a) ((b - 2) * a) + 1 + (2 * a + 4) + 1)
        + (mulRoundSteps a b (b - 1) (W - (b - 1) * a) ((b - 1) * a) + 1)
        + (a + 2 + 1)
        + (a + b * a + 4)
      = mulLoopSteps (b - 2) a b W
        + ((mulRoundSteps a b (b - 2) (W - (b - 2) * a) ((b - 2) * a) + 1 + (2 * a + 4) + 1)
        + ((mulRoundSteps a b (b - 1) (W - (b - 1) * a) ((b - 1) * a) + 1)
        + ((a + 2 + 1) + (a + b * a + 4)))) from by omega]
  rw [DTM.run_add mulMachine (mulLoopSteps (b - 2) a b W)
    ((mulRoundSteps a b (b - 2) (W - (b - 2) * a) ((b - 2) * a) + 1 + (2 * a + 4) + 1)
    + ((mulRoundSteps a b (b - 1) (W - (b - 1) * a) ((b - 1) * a) + 1)
    + ((a + 2 + 1) + (a + b * a + 4))))]
  rw [hloop]
  -- 循环步 `r = b-2`
  rw [DTM.run_add mulMachine
    (mulRoundSteps a b (b - 2) (W - (b - 2) * a) ((b - 2) * a) + 1 + (2 * a + 4) + 1)
    ((mulRoundSteps a b (b - 1) (W - (b - 1) * a) ((b - 1) * a) + 1)
    + ((a + 2 + 1) + (a + b * a + 4)))]
  rw [mulMachine_loop_step a b (b - 2) (W - (b - 2) * a) ((b - 2) * a) ha
    (by omega) hwa2 L R]
  rw [show b - 2 + 1 = b - 1 from by omega]
  rw [show (b - 2) * a + a = (b - 1) * a from by rw [hmulb2]]
  rw [show W - (b - 2) * a - a = W - (b - 1) * a from by rw [hmulb2, Nat.sub_sub]]
  -- 最后一轮
  rw [DTM.run_add mulMachine
    (mulRoundSteps a b (b - 1) (W - (b - 1) * a) ((b - 1) * a) + 1)
    ((a + 2 + 1) + (a + b * a + 4))]
  rw [mulMachine_phase_round a b (b - 1) (W - (b - 1) * a) ((b - 1) * a) ha
    (by omega) hb1 L R]
  rw [show b - 1 + 1 = b from by omega]
  rw [show (b - 1) * a + a = b * a from by rw [hmulb]]
  rw [show W - (b - 1) * a - a = W - b * a from by rw [hmulb, Nat.sub_sub]]
  -- 检测「耗尽」
  rw [hP2, hQ2]
  rw [DTM.run_add mulMachine (a + 2 + 1) (a + b * a + 4)]
  rw [mulMachine_phase_check_done a ha
    (List.replicate (b - 1) (some false) ++ (none :: (none :: L)))
    (List.replicate (b * a) (some false) ++
      (none :: (List.replicate (W - b * a) (none : Sym) ++ R)))]
  -- 收尾相位
  rw [mulMachine_phase_final a (b * a) ha (by omega)
    (List.replicate (b - 1) (some false) ++ (none :: (none :: L)))
    (List.replicate (W - b * a) (none : Sym) ++ R)]

/-- **接受态形态**：主定理的终点就是 `mulMachine.accept`（数值 27），便于装配层直接用
    「停在接受态」的语句调用。
    The endpoint of the main theorem is literally `mulMachine.accept`, so assembly layers can
    state it as "halts in the accept state". -/
theorem mulMachine_finish_accept (a b W : Nat) (ha : 1 ≤ a) (hb : 2 ≤ b) (hW : b * a ≤ W)
    (L R : List Sym) :
    mulMachine.run
      (mulLoopSteps (b - 2) a b W
        + (mulRoundSteps a b (b - 2) (W - (b - 2) * a) ((b - 2) * a) + 1 + (2 * a + 4) + 1)
        + (mulRoundSteps a b (b - 1) (W - (b - 1) * a) ((b - 1) * a) + 1)
        + (a + 2 + 1)
        + (a + b * a + 4))
      ⟨mulMachine.start, Tape.mk (mulL a b 0 0 L) (mulR 0 0 W R)⟩
      = ⟨mulMachine.accept,
          Tape.mk (List.replicate (b * a) (some true) ++
              (none :: (List.replicate a (some true) ++
                (none :: (some false ::
                  (List.replicate (b - 1) (some false) ++ (none :: (none :: L))))))))
            (none :: (List.replicate (W - b * a) (none : Sym) ++ R))⟩ := by
  rw [mulMachine_finish_run a b W ha hb hW L R]
  rfl
