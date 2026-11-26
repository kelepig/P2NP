/-
  文件：Pnp/Machine/Locality.lean
  File: Pnp/Machine/Locality.lean

  主题：图灵机的**局部性原理**——前 `K` 步内读写头最多离开原位 `K` 格，因此只要两张纸带
        在「距读写头 `K` 格以内」逐格一致，前 `K` 步的运行状态就完全相同（纸带也保持一致
        到剩余距离）。这是 E 机把「实际纸带（右侧还挂着输入副本）」与「理想纸带
        （`obsStart` 形态）」对上的基础工具。
  Topic: locality of computation — within `K` steps only the `K` cells around the head matter,
  so two tapes that agree near the head up to distance `K` yield identical runs for `K` steps.
  This lets E relate its real tape to the idealized `obsStart` tape.

  本文件给出（#227）：
    - `Tape.atR` / `Tape.atL`：从当前位置向右/向左第 `i` 格（越界视为空白）；
    - `Tape.AgreeNear`：距离 `n` 以内逐格一致；
    - 单步保持 `Tape.agreeNear_write` / `Tape.agreeNear_move`、`DTM.step_agree`；
    - 主定理 `DTM.run_agree_near` 与状态推论 `DTM.run_state_agree` / `DTM.accepts_at_agree`。
  Position-indexed tape agreement and its preservation through runs.
-/

import Pnp.Classes
import Pnp.Machine.ObsPhase

namespace Pnp

namespace Tape

/-- 从当前位置向右第 `i` 格（越界视为空白）。 Cell `i` to the right of the head. -/
def atR (t : Tape) (i : Nat) : Sym := t.right.getD i none

/-- 从当前位置向左第 `i` 格（越界视为空白）。 Cell `i` to the left of the head. -/
def atL (t : Tape) (i : Nat) : Sym := t.left.getD i none

/-- 两张纸带在「距读写头 `n` 格以内」逐格一致。
    Two tapes agree on every cell within distance `n` of the head. -/
def AgreeNear (n : Nat) (t1 t2 : Tape) : Prop :=
  (∀ i, i < n → t1.atR i = t2.atR i) ∧
  (∀ i, i < n → t1.atL i = t2.atL i)

/-- 当前格就是向右第 0 格。 The current cell is the right cell at index 0. -/
theorem read_eq_atR (t : Tape) : t.read = t.atR 0 := by
  cases t with
  | mk l r =>
      cases r with
      | nil => simp [read, atR]
      | cons x xs => simp [read, atR]

/-- 写入后当前格是新符号。 Writing puts `s` at the head. -/
theorem atR_write_zero (t : Tape) (s : Sym) : (t.write s).atR 0 = s := by
  cases t with
  | mk l r =>
      cases r with
      | nil => simp [write, atR]
      | cons x xs => simp [write, atR]

/-- 写入后第 `i+1` 格不变。 Writing leaves the other cells in place. -/
theorem atR_write_succ (t : Tape) (s : Sym) (i : Nat) :
    (t.write s).atR (i + 1) = t.atR (i + 1) := by
  cases t with
  | mk l r =>
      cases r with
      | nil => simp [write, atR]
      | cons x xs => simp [write, atR, List.getD_cons_succ]

/-- 写入不影响左侧。 Writing leaves the left side untouched. -/
theorem atL_write (t : Tape) (s : Sym) (i : Nat) : (t.write s).atL i = t.atL i := rfl

/-- 左移后左侧第 `i` 格是原来的第 `i+1` 格。 Shifting left drops one left cell. -/
theorem atL_moveLeft (t : Tape) (i : Nat) : t.moveLeft.atL i = t.atL (i + 1) := by
  cases t with
  | mk l r =>
      cases l with
      | nil => simp [moveLeft, atL]
      | cons x xs => simp [moveLeft, atL, List.getD_cons_succ]

/-- 左移后当前格是原来的左侧第 0 格。 After a left move the head cell was the nearest left cell. -/
theorem atR_moveLeft_zero (t : Tape) : t.moveLeft.atR 0 = t.atL 0 := by
  cases t with
  | mk l r =>
      cases l with
      | nil => simp [moveLeft, atR, atL]
      | cons x xs => simp [moveLeft, atR, atL]

/-- 左移后第 `i+1` 格是原来的第 `i` 格。 Left/right cells shift by one. -/
theorem atR_moveLeft_succ (t : Tape) (i : Nat) : t.moveLeft.atR (i + 1) = t.atR i := by
  cases t with
  | mk l r =>
      cases l with
      | nil => simp [moveLeft, atR]
      | cons x xs => simp [moveLeft, atR]

/-- 右移后左侧第 0 格是原来的当前格。 After a right move the nearest left cell was the head cell. -/
theorem atL_moveRight_zero (t : Tape) : t.moveRight.atL 0 = t.atR 0 := by
  cases t with
  | mk l r =>
      cases r with
      | nil => simp [moveRight, atR, atL]
      | cons x xs => simp [moveRight, atR, atL]

/-- 右移后左侧第 `i+1` 格是原来的第 `i` 格。 Left cells shift by one. -/
theorem atL_moveRight_succ (t : Tape) (i : Nat) :
    t.moveRight.atL (i + 1) = t.atL i := by
  cases t with
  | mk l r =>
      cases r with
      | nil => simp [moveRight, atL]
      | cons x xs => simp [moveRight, atL]

/-- 右移后右侧第 `i` 格是原来的第 `i+1` 格。 Right cells shift by one. -/
theorem atR_moveRight (t : Tape) (i : Nat) : t.moveRight.atR i = t.atR (i + 1) := by
  cases t with
  | mk l r =>
      cases r with
      | nil => simp [moveRight, atR]
      | cons x xs => simp [moveRight, atR, List.getD_cons_succ]

/-- 一致性可弱化：范围更大的一致性蕴含范围更小的。 Agreement weakens with the radius. -/
theorem agreeNear_mono {m n : Nat} (h : m ≤ n) {t1 t2 : Tape} (hA : AgreeNear n t1 t2) :
    AgreeNear m t1 t2 :=
  ⟨fun i hi => hA.1 i (by omega), fun i hi => hA.2 i (by omega)⟩

/-- 半径 ≥ 1 的一致性给出读数一致。 Nonzero agreement fixes the read symbol. -/
theorem agreeNear_read {n : Nat} {t1 t2 : Tape} (hA : AgreeNear (n + 1) t1 t2) :
    t1.read = t2.read := by
  rw [read_eq_atR, read_eq_atR]
  exact hA.1 0 (by omega)

/-- 同符号写入不改变一致性半径（只改动当前格，读头不动）。
    Writing the same symbol preserves the agreement radius (the head does not move). -/
theorem agreeNear_write {n : Nat} {t1 t2 : Tape} (hA : AgreeNear n t1 t2)
    (s : Sym) : AgreeNear n (t1.write s) (t2.write s) := by
  refine ⟨?_, ?_⟩
  · intro i hi
    cases i with
    | zero => rw [atR_write_zero, atR_write_zero]
    | succ j =>
        rw [atR_write_succ, atR_write_succ]
        exact hA.1 (j + 1) (by omega)
  · intro i hi
    rw [atL_write, atL_write]
    exact hA.2 i hi

/-- 同方向移动把半径 `n+1` 的一致性降到半径 `n`。
    Moving the same way drops the agreement radius by one. -/
theorem agreeNear_move {n : Nat} {t1 t2 : Tape} (hA : AgreeNear (n + 1) t1 t2)
    (d : Dir) : AgreeNear n (t1.move d) (t2.move d) := by
  cases d with
  | left =>
      show AgreeNear n t1.moveLeft t2.moveLeft
      refine ⟨?_, ?_⟩
      · intro i hi
        cases i with
        | zero =>
            rw [atR_moveLeft_zero, atR_moveLeft_zero]
            exact hA.2 0 (by omega)
        | succ j =>
            rw [atR_moveLeft_succ, atR_moveLeft_succ]
            exact hA.1 j (by omega)
      · intro i hi
        rw [atL_moveLeft, atL_moveLeft]
        exact hA.2 (i + 1) (by omega)
  | right =>
      show AgreeNear n t1.moveRight t2.moveRight
      refine ⟨?_, ?_⟩
      · intro i hi
        rw [atR_moveRight, atR_moveRight]
        exact hA.1 (i + 1) (by omega)
      · intro i hi
        cases i with
        | zero =>
            rw [atL_moveRight_zero, atL_moveRight_zero]
            exact hA.1 0 (by omega)
        | succ j =>
            rw [atL_moveRight_succ, atL_moveRight_succ]
            exact hA.2 j (by omega)
  | stay =>
      show AgreeNear n t1 t2
      exact agreeNear_mono (by omega) hA

end Tape

namespace DTM

variable {q : Nat}

/-- 状态相同 + 半径 `n+1` 的纸带一致性 ⇒ 一步之后状态仍相同、半径 `n` 的纸带仍一致。
    One step preserves state equality and degrades near-agreement by one. -/
theorem step_agree (M : DTM q) {n : Nat} {c1 c2 : Config q}
    (hs : c1.state = c2.state) (hA : Tape.AgreeNear (n + 1) c1.tape c2.tape) :
    (M.stepConfig c1).state = (M.stepConfig c2).state ∧
      Tape.AgreeNear n (M.stepConfig c1).tape (M.stepConfig c2).tape := by
  have hr : c1.tape.read = c2.tape.read := Tape.agreeNear_read hA
  have hstep : M.step c1.state c1.tape.read = M.step c2.state c2.tape.read := by
    rw [hs, hr]
  refine ⟨?_, ?_⟩
  · rw [stepConfig_state, stepConfig_state, hstep]
  · unfold DTM.stepConfig
    rw [hstep]
    exact Tape.agreeNear_move (Tape.agreeNear_write hA _) _

/-- **局部性主定理**：两张纸带在半径 `n+k` 内一致、状态相同 ⇒ 运行 `k` 步后状态相同，
    纸带在半径 `n` 内仍一致。
    Locality: agreement within radius `n+k` gives equal states after `k` steps and agreement
    within radius `n`. -/
theorem run_agree_near (M : DTM q) (k : Nat) :
    ∀ (n : Nat) (c1 c2 : Config q), c1.state = c2.state →
      Tape.AgreeNear (n + k) c1.tape c2.tape →
      (M.run k c1).state = (M.run k c2).state ∧
        Tape.AgreeNear n (M.run k c1).tape (M.run k c2).tape := by
  induction k with
  | zero =>
      intro n c1 c2 hs hA
      rw [Nat.add_zero] at hA
      exact ⟨hs, hA⟩
  | succ k ih =>
      intro n c1 c2 hs hA
      rw [show n + (k + 1) = (n + k) + 1 from by omega] at hA
      have hh : M.halted c1 = M.halted c2 := by unfold DTM.halted; rw [hs]
      by_cases hc : M.halted c1 = true
      · -- 已停机：两边都冻结在原格局
        have hc2 : M.halted c2 = true := by rw [← hh]; exact hc
        rw [run_of_halted M c1 hc (k + 1), run_of_halted M c2 hc2 (k + 1)]
        exact ⟨hs, Tape.agreeNear_mono (by omega) hA⟩
      · -- 未停机：两边各走一步，再用归纳假设
        have hc0 : M.halted c1 = false := by
          cases h : M.halted c1 with
          | false => rfl
          | true => exact absurd h hc
        have hc2 : M.halted c2 = false := by rw [← hh]; exact hc0
        rw [run_succ_of_not_halted M k c1 hc0, run_succ_of_not_halted M k c2 hc2]
        obtain ⟨hst, hAg⟩ := step_agree M hs hA
        exact ih n (M.stepConfig c1) (M.stepConfig c2) hst hAg

/-- **状态级推论**：半径 `K` 内一致 ⇒ 前 `K` 步（任意 `k ≤ K`）状态相同。
    State-level corollary: agreement within radius `K` gives equal states after `k ≤ K` steps. -/
theorem run_state_agree (M : DTM q) (K k : Nat) (hK : k ≤ K) (c1 c2 : Config q)
    (hs : c1.state = c2.state) (hA : Tape.AgreeNear K c1.tape c2.tape) :
    (M.run k c1).state = (M.run k c2).state := by
  have h := (run_agree_near M k (K - k) c1 c2 hs (by
    rw [Nat.sub_add_cancel hK]
    exact hA)).1
  exact h

/-- **判定级推论**：半径 `K` 内一致 ⇒ 跑满 `K` 步后接受与否相同。
    Verdict-level corollary: agreement within radius `K` preserves acceptance after `K` steps. -/
theorem run_accept_agree (M : DTM q) (K : Nat) (c1 c2 : Config q)
    (hs : c1.state = c2.state) (hA : Tape.AgreeNear K c1.tape c2.tape) :
    ((M.run K c1).state = M.accept ↔ (M.run K c2).state = M.accept) := by
  have h := run_state_agree M K K (Nat.le_refl K) c1 c2 hs hA
  rw [h]

end DTM


/-! ## 左副本绝缘：远端左尾不影响运行（头不触底的条件下） -/

namespace Tape

/-- 写入不改变左侧格数。 Writing preserves the left length. -/
theorem leftLen_write (t : Tape) (s : Sym) : (t.write s).left.length = t.left.length := rfl

/-- 左移使左侧格数减一（空时保持 0）。 A left move drops one left cell. -/
theorem leftLen_moveLeft (t : Tape) : t.moveLeft.left.length = t.left.length - 1 := by
  cases t with
  | mk l r =>
      cases l with
      | nil => simp [moveLeft]
      | cons x xs => simp [moveLeft]

/-- 右移使左侧格数加一。 A right move adds one left cell. -/
theorem leftLen_moveRight (t : Tape) : t.moveRight.left.length = t.left.length + 1 := by
  cases t with
  | mk l r =>
      cases r with
      | nil => simp [moveRight]
      | cons x xs => simp [moveRight]

/-- `t2` 是 `t1` 在**远端左侧**追加一段尾巴后的纸带：右侧完全相同，左侧多出一段。
    `t2` is `t1` with an extra far-left tail; the head-side (right) parts agree exactly. -/
def PadLeft (t1 t2 : Tape) : Prop :=
  t2.right = t1.right ∧ ∃ C : List Sym, t2.left = t1.left ++ C

/-- 左副本绝缘下读数相同。 Under a left tail the read symbol is unchanged. -/
theorem padLeft_read {t1 t2 : Tape} (h : PadLeft t1 t2) : t1.read = t2.read := by
  obtain ⟨hr, _⟩ := h
  rw [read, read, hr]

/-- 同符号写入保持左副本绝缘。 Writing preserves a left tail. -/
theorem padLeft_write {t1 t2 : Tape} (h : PadLeft t1 t2) (s : Sym) :
    PadLeft (t1.write s) (t2.write s) := by
  obtain ⟨hr, C, hl⟩ := h
  refine ⟨?_, C, ?_⟩
  · show s :: t2.right.tail = s :: t1.right.tail
    rw [hr]
  · show t2.left = t1.left ++ C
    exact hl

/-- 右移保持左副本绝缘。 A right move preserves a left tail. -/
theorem padLeft_moveRight {t1 t2 : Tape} (h : PadLeft t1 t2) :
    PadLeft t1.moveRight t2.moveRight := by
  obtain ⟨hr, C, hl⟩ := h
  obtain ⟨l1, r1⟩ := t1
  obtain ⟨l2, r2⟩ := t2
  simp only at hr hl
  subst hl
  subst hr
  cases r2 with
  | nil => simp only [moveRight]; exact ⟨rfl, C, by simp⟩
  | cons x xs => simp only [moveRight]; exact ⟨rfl, C, by simp⟩

/-- 左移保持左副本绝缘（前提：理想纸带左侧非空）。
    A left move preserves a left tail provided the ideal tape still has a left cell. -/
theorem padLeft_moveLeft {t1 t2 : Tape} (h : PadLeft t1 t2) (hne : t1.left ≠ []) :
    PadLeft t1.moveLeft t2.moveLeft := by
  obtain ⟨hr, C, hl⟩ := h
  obtain ⟨l1, r1⟩ := t1
  obtain ⟨l2, r2⟩ := t2
  simp only at hr hl
  subst hl
  subst hr
  cases l1 with
  | nil => exact absurd rfl hne
  | cons x xs =>
      simp only [moveLeft]
      exact ⟨rfl, C, by simp⟩

/-- 同方向移动保持左副本绝缘（左移需要理想纸带左侧非空）。
    Moving the same way preserves a left tail (the left move needs a nonempty left cell). -/
theorem padLeft_move {t1 t2 : Tape} (h : PadLeft t1 t2) (d : Dir) (hne : t1.left ≠ []) :
    PadLeft (t1.move d) (t2.move d) := by
  cases d with
  | left => exact padLeft_moveLeft h hne
  | right =>
      show PadLeft t1.moveRight t2.moveRight
      exact padLeft_moveRight h
  | stay =>
      show PadLeft t1 t2
      exact h

/-- **弱化的移动引理**：只有在左端为空时禁止左移；实际只有左移会破坏左尾绝缘。
    Weaker move lemma: only a left move at the empty left end can break insulation. -/
theorem padLeft_step {t1 t2 : Tape} (h : PadLeft t1 t2) (s : Sym) (d : Dir)
    (hok : t1.left = [] → d ≠ Dir.left) :
    PadLeft ((t1.write s).move d) ((t2.write s).move d) := by
  have hw := padLeft_write h s
  cases d with
  | left =>
      have hne : t1.left ≠ [] := by
        intro hnil
        exact hok hnil rfl
      show PadLeft ((t1.write s).moveLeft) ((t2.write s).moveLeft)
      exact padLeft_moveLeft hw (by simpa [write] using hne)
  | right =>
      show PadLeft ((t1.write s).moveRight) ((t2.write s).moveRight)
      exact padLeft_moveRight hw
  | stay =>
      show PadLeft (t1.write s) (t2.write s)
      exact hw

end Tape

namespace DTM

variable {q : Nat}

/-- 停机判定只依赖状态。 Halting depends only on the state. -/
theorem halted_congr (M : DTM q) {c1 c2 : Config q} (hs : c1.state = c2.state) :
    M.halted c1 = M.halted c2 := by
  unfold DTM.halted
  rw [hs]

/-- 一步保持左副本绝缘（且状态保持相等）。
    One step preserves left-tail insulation and state equality. -/
theorem step_padLeft (M : DTM q) {c1 c2 : Config q}
    (hs : c1.state = c2.state) (hP : Tape.PadLeft c1.tape c2.tape)
    (hne : c1.tape.left ≠ []) :
    (M.stepConfig c1).state = (M.stepConfig c2).state ∧
      Tape.PadLeft (M.stepConfig c1).tape (M.stepConfig c2).tape := by
  have hr : c1.tape.read = c2.tape.read := Tape.padLeft_read hP
  have hstep : M.step c1.state c1.tape.read = M.step c2.state c2.tape.read := by
    rw [hs, hr]
  refine ⟨?_, ?_⟩
  · rw [stepConfig_state, stepConfig_state, hstep]
  · unfold DTM.stepConfig
    rw [hstep]
    exact Tape.padLeft_move (Tape.padLeft_write hP _) _ hne

/-- **左副本绝缘主定理**：两张纸带只差远端左尾（右侧完全相同），状态相同，且理想纸带
    前 `k` 步的左侧始终非空 ⇒ 跑 `k` 步后状态相同。
    Left-tail insulation: a far-left tail never changes the state trajectory, provided the
    ideal tape keeps a nonempty left cell throughout. -/
theorem run_state_eq_of_padLeft (M : DTM q) (k : Nat) :
    ∀ (c1 c2 : Config q), c1.state = c2.state →
      Tape.PadLeft c1.tape c2.tape →
      (∀ j, j < k → (M.run j c1).tape.left ≠ []) →
      (M.run k c1).state = (M.run k c2).state := by
  induction k with
  | zero =>
      intro c1 c2 hs _ _
      exact hs
  | succ K ih =>
      intro c1 c2 hs hP hne
      by_cases hc : M.halted c1 = true
      · -- 已停机：两边都冻结
        have hc2 : M.halted c2 = true := by rw [← halted_congr M hs]; exact hc
        rw [run_of_halted M c1 hc (K + 1), run_of_halted M c2 hc2 (K + 1)]
        exact hs
      · -- 未停机：两边各走一步
        have hc0 : M.halted c1 = false := by
          cases h : M.halted c1 with
          | false => rfl
          | true => exact absurd h hc
        have hc2 : M.halted c2 = false := by rw [← halted_congr M hs]; exact hc0
        rw [run_succ_of_not_halted M K c1 hc0, run_succ_of_not_halted M K c2 hc2]
        have hstep := step_padLeft M hs hP (hne 0 (by omega))
        have hne' : ∀ j, j < K → (M.run j (M.stepConfig c1)).tape.left ≠ [] := by
          intro j hj
          have h1 := hne (j + 1) (by omega)
          rw [run_succ_of_not_halted M j c1 hc0] at h1
          exact h1
        exact ih (M.stepConfig c1) (M.stepConfig c2) hstep.1 hstep.2 hne'

/-- **判定级推论（左副本绝缘）**：跑满 `k` 步后接受与否相同。
    Verdict corollary for left-tail insulation. -/
theorem run_accept_eq_of_padLeft (M : DTM q) (k : Nat) (c1 c2 : Config q)
    (hs : c1.state = c2.state) (hP : Tape.PadLeft c1.tape c2.tape)
    (hne : ∀ j, j < k → (M.run j c1).tape.left ≠ []) :
    ((M.run k c1).state = M.accept ↔ (M.run k c2).state = M.accept) := by
  rw [run_state_eq_of_padLeft M k c1 c2 hs hP hne]

end DTM


/-! ## 运行相位机的逃逸端点（E 机逐分支读判据用） -/

namespace DTM

variable {q : Nat}

/-- 逃生态是停机态，一旦到达就冻结在原格局。
    The escape state halts, so once reached the configuration is frozen. -/
theorem obsPhase_esc_persists (q b : Nat) (M : NTM q) (t : Tape) (n : Nat) :
    (obsPhase q b M).run n ⟨obsEsc q b, t⟩ = ⟨obsEsc q b, t⟩ :=
  run_of_halted (obsPhase q b M) _ (obsPhase_halted_esc q b M t) n

/-- **失败端点**：观察机在第 `K` 步停在失败哨兵 ⇒ 运行相位机在第 `K+1` 步停在逃生态。
    Fail endpoint: if `simObs` sits at the fail sentinel after `K` steps, `obsPhase` sits at
    the escape state after `K + 1` steps. -/
theorem obsPhase_esc_of_simObs_fail (q b : Nat) (M : NTM q) (K : Nat)
    (c : Config (stateCountO q b))
    (h : ((simObs q b M).run K c).state = obsFail q b) :
    ((obsPhase q b M).run (K + 1) ⟨embOb q b c.state, c.tape⟩).state = obsEsc q b := by
  rcases obsPhase_run_config_proj q b M K c with hl | ⟨hr, _⟩
  · -- 尚未逃逸：第 `K` 步是嵌入的失败哨兵，再一步即逃逸
    have hcfg : (obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩
        = ⟨embOb q b (obsFail q b), ((simObs q b M).run K c).tape⟩ := by
      rw [hl, h]
    have hesc := obsPhase_escape_once q b M ((simObs q b M).run K c) h 0
    have hesc' : ((obsPhase q b M).run (0 + 1)
        ⟨embOb q b ((simObs q b M).run K c).state,
          ((simObs q b M).run K c).tape⟩).state = obsEsc q b :=
      congrArg Config.state hesc
    have hesc2 : ((obsPhase q b M).run (0 + 1)
        ⟨embOb q b (obsFail q b), ((simObs q b M).run K c).tape⟩).state = obsEsc q b := by
      rw [← h]
      exact hesc'
    rw [DTM.run_add (obsPhase q b M) K 1, hcfg, hesc2]
  · -- 已经逃逸：冻结在逃生态
    have hstR : ((obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩).state
        = (obsPhase q b M).reject := by
      rw [hr]
      rfl
    have hhalt := halted_of_accept_or_reject (obsPhase q b M) _ (Or.inr hstR)
    rw [DTM.run_add (obsPhase q b M) K 1,
      run_of_halted (obsPhase q b M) _ hhalt]
    exact hr

end DTM


namespace DTM

variable {q : Nat}

/-- **弱化版一步保持**：左端为空且下一步不左移时，左尾绝缘保持。
    Weak one-step preservation: insulation survives an empty left end as long as the move
    is not left. -/
theorem step_padLeft' (M : DTM q) {c1 c2 : Config q}
    (hs : c1.state = c2.state) (hP : Tape.PadLeft c1.tape c2.tape)
    (hok : c1.tape.left = [] →
      (M.step c1.state c1.tape.read).2.2 ≠ Dir.left) :
    (M.stepConfig c1).state = (M.stepConfig c2).state ∧
      Tape.PadLeft (M.stepConfig c1).tape (M.stepConfig c2).tape := by
  have hr : c1.tape.read = c2.tape.read := Tape.padLeft_read hP
  have hstep : M.step c1.state c1.tape.read = M.step c2.state c2.tape.read := by
    rw [hs, hr]
  have hok2 : c1.tape.left = [] → (M.step c2.state c2.tape.read).2.2 ≠ Dir.left := by
    intro hnil hleft
    exact hok hnil (by rw [hstep]; exact hleft)
  refine ⟨?_, ?_⟩
  · rw [stepConfig_state, stepConfig_state, hstep]
  · unfold DTM.stepConfig
    rw [hstep]
    exact Tape.padLeft_step hP _ _ hok2

/-- **弱化版左副本绝缘主定理**：只需「左端为空时机器人不左移」，状态轨迹就与远端左尾无关。
    Weakened insulation: the trajectory is independent of the far-left tail provided the
    machine never moves left while standing on the leftmost cell. -/
theorem run_state_eq_of_padLeft' (M : DTM q) (k : Nat) :
    ∀ (c1 c2 : Config q), c1.state = c2.state →
      Tape.PadLeft c1.tape c2.tape →
      (∀ j, j < k → (M.run j c1).tape.left = [] →
        (M.step (M.run j c1).state (M.run j c1).tape.read).2.2 ≠ Dir.left) →
      (M.run k c1).state = (M.run k c2).state := by
  induction k with
  | zero =>
      intro c1 c2 hs _ _
      exact hs
  | succ K ih =>
      intro c1 c2 hs hP hok
      by_cases hc : M.halted c1 = true
      · have hc2 : M.halted c2 = true := by rw [← halted_congr M hs]; exact hc
        rw [run_of_halted M c1 hc (K + 1), run_of_halted M c2 hc2 (K + 1)]
        exact hs
      · have hc0 : M.halted c1 = false := by
          cases h : M.halted c1 with
          | false => rfl
          | true => exact absurd h hc
        have hc2 : M.halted c2 = false := by rw [← halted_congr M hs]; exact hc0
        rw [run_succ_of_not_halted M K c1 hc0, run_succ_of_not_halted M K c2 hc2]
        have hstep := step_padLeft' M hs hP (hok 0 (by omega))
        have hok' : ∀ j, j < K → (M.run j (M.stepConfig c1)).tape.left = [] →
            (M.step (M.run j (M.stepConfig c1)).state
              (M.run j (M.stepConfig c1)).tape.read).2.2 ≠ Dir.left := by
          intro j hj hnil
          have h1 := hok (j + 1) (by omega)
          rw [run_succ_of_not_halted M j c1 hc0] at h1
          exact h1 hnil
        exact ih (M.stepConfig c1) (M.stepConfig c2) hstep.1 hstep.2 hok'


/-- **一步最多消耗一格左侧**：左长每步至多减一。
    One step drops at most one left cell. -/
theorem step_leftLen (M : DTM q) (c : Config q) :
    (M.stepConfig c).tape.left.length ≥ c.tape.left.length - 1 := by
  unfold DTM.stepConfig
  generalize hst : M.step c.state c.tape.read = st
  obtain ⟨q', s, d⟩ := st
  cases d with
  | left =>
      show ((c.tape.write s).moveLeft).left.length ≥ c.tape.left.length - 1
      rw [Tape.leftLen_moveLeft, Tape.leftLen_write]
      omega
  | right =>
      show ((c.tape.write s).moveRight).left.length ≥ c.tape.left.length - 1
      rw [Tape.leftLen_moveRight, Tape.leftLen_write]
      omega
  | stay =>
      show (c.tape.write s).left.length ≥ c.tape.left.length - 1
      rw [Tape.leftLen_write]
      omega

/-- **左长下界累积**：跑 `k` 步后左长至少是初始左长减 `k`。
    Left-length lower bound: `k` steps consume at most `k` left cells. -/
theorem run_leftLen_ge (M : DTM q) (k : Nat) :
    ∀ c : Config q, (M.run k c).tape.left.length + k ≥ c.tape.left.length := by
  induction k with
  | zero =>
      intro c
      exact Nat.le_refl _
  | succ K ih =>
      intro c
      by_cases hc : M.halted c = true
      · rw [run_of_halted M c hc]
        omega
      · have hc0 : M.halted c = false := by
          cases h : M.halted c with
          | false => rfl
          | true => exact absurd h hc
        rw [run_succ_of_not_halted M K c hc0]
        have h1 := step_leftLen M c
        have h2 := ih (M.stepConfig c)
        omega

/-- 初始左长大于步数 ⇒ 运行中左侧始终非空。
    A long enough initial left side never empties within `k` steps. -/
theorem left_ne_of_run (M : DTM q) (k j : Nat) (hj : j ≤ k) (c : Config q)
    (h : k + 1 ≤ c.tape.left.length) : (M.run j c).tape.left ≠ [] := by
  intro hnil
  have hge := run_leftLen_ge M j c
  have h0 : (M.run j c).tape.left.length = 0 := by rw [hnil]; rfl
  omega

/-- **左界安全性的长度判据**：初始左长 ≥ `K+1` ⇒ 「左端为空还左移」不可能发生。
    Length criterion for left safety. -/
theorem left_safe_of_len (M : DTM q) (K : Nat) (c : Config q)
    (h : K + 1 ≤ c.tape.left.length) :
    ∀ j, j < K → (M.run j c).tape.left = [] →
      (M.step (M.run j c).state (M.run j c).tape.read).2.2 ≠ Dir.left := by
  intro j hj hnil
  exact absurd hnil (left_ne_of_run M K j (by omega) c h)

/-- **长度版的左尾判定搬运**：初始左长 ≥ `K+1` 时，远端左尾不影响 `K` 步内的接受判定。
    Length-based verdict transfer under a far-left tail. -/
theorem run_accept_eq_of_padLeft_len (M : DTM q) (K : Nat) (c1 c2 : Config q)
    (hs : c1.state = c2.state) (hP : Tape.PadLeft c1.tape c2.tape)
    (h : K + 1 ≤ c1.tape.left.length) :
    ((M.run K c1).state = M.accept ↔ (M.run K c2).state = M.accept) := by
  rw [run_state_eq_of_padLeft' M K c1 c2 hs hP (left_safe_of_len M K c1 h)]

end DTM


/-! ## 右副本绝缘：远端右尾不影响运行（右侧不触底的条件下）

    与左副本绝缘镜像。E 机把输入副本挂在**区域右侧**（docs/07 #146 布局），
    实际纸带 = 理想纸带 ++ 远端右尾；本节的工具用于把实际运行搬回理想运行。
    注意对称差异：读数取自右侧表头，故右尾绝缘要求**每一步右侧都非空**
    （左侧绝缘只需「左端为空时不左移」，见 #230）。

    Mirror of left-tail insulation. E keeps the read-only input copy to the **right** of the
    region (layout #146), so the actual tape is the ideal tape followed by a far-right tail.
    Symmetry note: reads come from the head of `right`, hence every step needs a nonempty
    right side; the obligation is stronger than its left-side counterpart. -/

namespace Tape

/-- 右副本绝缘：`t2` 是 `t1` 在**远端右侧**追加一段尾巴后的纸带（左侧完全相同，右侧多一段）。
    Right-tail insulation: `t2` is `t1` with an extra far-right tail. -/
def PadRight (t1 t2 : Tape) : Prop :=
  t1.left = t2.left ∧ ∃ C : List Sym, t2.right = t1.right ++ C

/-- 右侧非空时读数相同。读数相同需要右侧非空：空右侧读空白，而 `t2` 读到尾巴首符号。
    With a nonempty right side the two tapes read the same symbol. -/
theorem padRight_read {t1 t2 : Tape} (h : PadRight t1 t2) (hne : t1.right ≠ []) :
    t1.read = t2.read := by
  obtain ⟨_, C, hr⟩ := h
  obtain ⟨l1, r1⟩ := t1
  simp only at hne hr
  cases r1 with
  | nil => exfalso; exact hne rfl
  | cons a as => simp [read, hr]

/-- 右侧非空时同符号写入保持右副本绝缘。 A write preserves a right tail (nonempty right). -/
theorem padRight_write {t1 t2 : Tape} (h : PadRight t1 t2) (s : Sym)
    (hne : t1.right ≠ []) : PadRight (t1.write s) (t2.write s) := by
  obtain ⟨hl, C, hr⟩ := h
  refine ⟨hl, C, ?_⟩
  cases h1 : t1.right with
  | nil => exfalso; exact hne h1
  | cons a as =>
      have h2 : t2.right = a :: (as ++ C) := by rw [hr, h1, List.cons_append]
      show s :: t2.right.tail = s :: t1.right.tail ++ C
      rw [h2, h1]
      simp

/-- 左移保持右副本绝缘（左侧相同的部分同步变化）。 A left move preserves a right tail. -/
theorem padRight_moveLeft {t1 t2 : Tape} (h : PadRight t1 t2) :
    PadRight t1.moveLeft t2.moveLeft := by
  obtain ⟨hl, C, hr⟩ := h
  obtain ⟨l1, r1⟩ := t1
  obtain ⟨l2, r2⟩ := t2
  simp only at hl hr
  subst hl
  subst hr
  cases l1 with
  | nil => simp only [moveLeft]; exact ⟨rfl, C, by simp⟩
  | cons x xs => simp only [moveLeft]; exact ⟨rfl, C, by simp⟩

/-- 右侧非空时右移保持右副本绝缘。 A right move preserves a right tail (nonempty right). -/
theorem padRight_moveRight {t1 t2 : Tape} (h : PadRight t1 t2) (hne : t1.right ≠ []) :
    PadRight t1.moveRight t2.moveRight := by
  obtain ⟨hl, C, hr⟩ := h
  obtain ⟨l1, r1⟩ := t1
  obtain ⟨l2, r2⟩ := t2
  simp only at hl hr
  subst hl
  subst hr
  cases r1 with
  | nil => exfalso; exact hne rfl
  | cons a as => simp only [moveRight]; exact ⟨rfl, C, by simp⟩

/-- 同方向移动保持右副本绝缘（右移要求右侧非空）。
    Moving the same way preserves a right tail (the right move needs a nonempty right). -/
theorem padRight_move {t1 t2 : Tape} (h : PadRight t1 t2) (d : Dir) (hne : t1.right ≠ []) :
    PadRight (t1.move d) (t2.move d) := by
  cases d with
  | left =>
      show PadRight t1.moveLeft t2.moveLeft
      exact padRight_moveLeft h
  | right =>
      show PadRight t1.moveRight t2.moveRight
      exact padRight_moveRight h hne
  | stay =>
      show PadRight t1 t2
      exact h

end Tape

namespace DTM

variable {q : Nat}

/-- 一步保持右副本绝缘（前提：当前右侧非空）。
    One step preserves right-tail insulation provided the right side is nonempty. -/
theorem step_padRight (M : DTM q) {c1 c2 : Config q}
    (hs : c1.state = c2.state) (hP : Tape.PadRight c1.tape c2.tape)
    (hne : c1.tape.right ≠ []) :
    (M.stepConfig c1).state = (M.stepConfig c2).state ∧
      Tape.PadRight (M.stepConfig c1).tape (M.stepConfig c2).tape := by
  have hr : c1.tape.read = c2.tape.read := Tape.padRight_read hP hne
  have hstep : M.step c1.state c1.tape.read = M.step c2.state c2.tape.read := by
    rw [hs, hr]
  refine ⟨?_, ?_⟩
  · rw [stepConfig_state, stepConfig_state, hstep]
  · unfold DTM.stepConfig
    rw [hstep]
    exact Tape.padRight_move (Tape.padRight_write hP _ hne) _ (by simp [Tape.write])

/-- **右副本绝缘主定理**：两张纸带只差远端右尾（左侧完全相同），状态相同，且理想纸带
    前 `k` 步的右侧始终非空 ⇒ 跑 `k` 步后状态相同。
    Right-tail insulation: a far-right tail never changes the state trajectory, provided the
    ideal tape keeps a nonempty right side throughout. -/
theorem run_state_eq_of_padRight (M : DTM q) (k : Nat) :
    ∀ (c1 c2 : Config q), c1.state = c2.state →
      Tape.PadRight c1.tape c2.tape →
      (∀ j, j < k → (M.run j c1).tape.right ≠ []) →
      (M.run k c1).state = (M.run k c2).state := by
  induction k with
  | zero =>
      intro c1 c2 hs _ _
      exact hs
  | succ K ih =>
      intro c1 c2 hs hP hne
      by_cases hc : M.halted c1 = true
      · have hc2 : M.halted c2 = true := by rw [← halted_congr M hs]; exact hc
        rw [run_of_halted M c1 hc (K + 1), run_of_halted M c2 hc2 (K + 1)]
        exact hs
      · have hc0 : M.halted c1 = false := by
          cases h : M.halted c1 with
          | false => rfl
          | true => exact absurd h hc
        have hc2 : M.halted c2 = false := by rw [← halted_congr M hs]; exact hc0
        rw [run_succ_of_not_halted M K c1 hc0, run_succ_of_not_halted M K c2 hc2]
        have hstep := step_padRight M hs hP (hne 0 (by omega))
        have hne' : ∀ j, j < K → (M.run j (M.stepConfig c1)).tape.right ≠ [] := by
          intro j hj
          have h1 := hne (j + 1) (by omega)
          rw [run_succ_of_not_halted M j c1 hc0] at h1
          exact h1
        exact ih (M.stepConfig c1) (M.stepConfig c2) hstep.1 hstep.2 hne'

/-- **判定级推论（右副本绝缘）**：跑满 `k` 步后接受与否相同。
    Verdict corollary for right-tail insulation. -/
theorem run_accept_eq_of_padRight (M : DTM q) (k : Nat) (c1 c2 : Config q)
    (hs : c1.state = c2.state) (hP : Tape.PadRight c1.tape c2.tape)
    (hne : ∀ j, j < k → (M.run j c1).tape.right ≠ []) :
    ((M.run k c1).state = M.accept ↔ (M.run k c2).state = M.accept) := by
  rw [run_state_eq_of_padRight M k c1 c2 hs hP hne]

end DTM

namespace Tape

/-- 写入不减少右侧格数（右侧非空时保持不变，空时补一格）。
    A write never shrinks the right side. -/
theorem rightLen_write (t : Tape) (s : Sym) (h : t.right ≠ []) :
    (t.write s).right.length = t.right.length := by
  obtain ⟨l, r⟩ := t
  cases r with
  | nil => exact absurd rfl h
  | cons a as => rfl

/-- 右移使右侧格数减一（空时保持 0）。 A right move drops one right cell. -/
theorem rightLen_moveRight (t : Tape) : t.moveRight.right.length = t.right.length - 1 := by
  cases t with
  | mk l r =>
      cases r with
      | nil => simp [moveRight]
      | cons a as => simp [moveRight]

/-- 左移使右侧格数加一。 A left move adds one right cell. -/
theorem rightLen_moveLeft (t : Tape) : t.moveLeft.right.length = t.right.length + 1 := by
  cases t with
  | mk l r =>
      cases l with
      | nil => simp [moveLeft]
      | cons x xs => simp [moveLeft]

end Tape

namespace DTM

variable {q : Nat}

/-- **一步最多消耗一格右侧**：右长每步至多减一。
    One step drops at most one right cell. -/
theorem step_rightLen (M : DTM q) (c : Config q) :
    (M.stepConfig c).tape.right.length ≥ c.tape.right.length - 1 := by
  unfold DTM.stepConfig
  generalize hst : M.step c.state c.tape.read = st
  obtain ⟨q', s, d⟩ := st
  have hw : (c.tape.write s).right.length ≥ c.tape.right.length - 1 := by
    cases h : c.tape.right with
    | nil => simp [Tape.write, h]
    | cons a as =>
        have hne : c.tape.right ≠ [] := by rw [h]; exact List.cons_ne_nil a as
        have hlen : c.tape.right.length = (a :: as).length := by rw [h]
        have hl := Tape.rightLen_write c.tape s hne
        omega
  cases d with
  | left =>
      show ((c.tape.write s).moveLeft).right.length ≥ c.tape.right.length - 1
      rw [Tape.rightLen_moveLeft]
      omega
  | right =>
      show ((c.tape.write s).moveRight).right.length ≥ c.tape.right.length - 1
      rw [Tape.rightLen_moveRight]
      cases h : c.tape.right with
      | nil => simp [Tape.write, h]
      | cons a as =>
          have hne : c.tape.right ≠ [] := by rw [h]; exact List.cons_ne_nil a as
          have hlen : c.tape.right.length = (a :: as).length := by rw [h]
          have hl := Tape.rightLen_write c.tape s hne
          omega
  | stay =>
      show (c.tape.write s).right.length ≥ c.tape.right.length - 1
      exact hw

/-- **右长下界累积**：跑 `k` 步后右长至少是初始右长减 `k`。
    Right-length lower bound: `k` steps consume at most `k` right cells. -/
theorem run_rightLen_ge (M : DTM q) (k : Nat) :
    ∀ c : Config q, (M.run k c).tape.right.length + k ≥ c.tape.right.length := by
  induction k with
  | zero =>
      intro c
      exact Nat.le_refl _
  | succ K ih =>
      intro c
      by_cases hc : M.halted c = true
      · rw [run_of_halted M c hc]
        omega
      · have hc0 : M.halted c = false := by
          cases h : M.halted c with
          | false => rfl
          | true => exact absurd h hc
        rw [run_succ_of_not_halted M K c hc0]
        have h1 := step_rightLen M c
        have h2 := ih (M.stepConfig c)
        omega

/-- **右侧安全性的长度判据**：初始右长 ≥ `K+1` ⇒ 前 `K` 步右侧始终非空。
    Length criterion for right safety: a long enough initial right side never empties. -/
theorem right_safe_of_len (M : DTM q) (K : Nat) (c : Config q)
    (h : K + 1 ≤ c.tape.right.length) :
    ∀ j, j < K → (M.run j c).tape.right ≠ [] := by
  intro j hj hnil
  have hge := run_rightLen_ge M j c
  have h0 : (M.run j c).tape.right.length = 0 := by rw [hnil]; rfl
  omega

/-- **长度版的右尾判定搬运**：初始右长 ≥ `K+1` 时，远端右尾不影响 `K` 步内的接受判定。
    Length-based verdict transfer under a far-right tail. -/
theorem run_accept_eq_of_padRight_len (M : DTM q) (K : Nat) (c1 c2 : Config q)
    (hs : c1.state = c2.state) (hP : Tape.PadRight c1.tape c2.tape)
    (h : K + 1 ≤ c1.tape.right.length) :
    ((M.run K c1).state = M.accept ↔ (M.run K c2).state = M.accept) := by
  rw [run_state_eq_of_padRight M K c1 c2 hs hP (right_safe_of_len M K c1 h)]

end DTM

end Pnp
