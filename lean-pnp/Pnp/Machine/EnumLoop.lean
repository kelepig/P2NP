/-
  文件：Pnp/Machine/EnumLoop.lean
  主题：枚举循环机 `enumLoop`（加一 ↔ 回块首，溢出则清零停机）。

  状态布局（共 12 个状态）：
    - 0–3：`binIncFlag` 加一相位（0 扫描，1 正常完成，2 溢出，3 未用）；
    - 4–7：`rewindIntoBlock` 回块首相位（4 跨入，5 扫描，6 接受，7 拒绝）；
    - 8–11：`resetZeros` 清零相位（8 跨入，9 扫描，10 接受，11 拒绝）。

  路由：
    - 加一正常完成（1）→ 回块首相位（4）；
    - 回块首完成（6）→ 回到加一相位起点（0），开始下一轮；
    - 加一溢出（2）→ 清零相位（8），清零完成（10）即整机接受。

  因此整机的接受状态 10 只在「计数器溢出」时到达；正常情况下它永远在
  「加一 → 回块首 → 加一」之间循环。
-/

import Pnp.Machine.EnumRound
import Pnp.Machine.ResetZeros
import Pnp.Machine.Scan

namespace Pnp

namespace DTM

/-- 加一相位状态嵌入（0–3 → 0–3）。 -/
def loopIncState (s : Fin 4) : Fin 12 := ⟨s.val, by have := s.isLt; omega⟩

/-- 回块首相位状态嵌入（0–3 → 4–7）。 -/
def loopRewState (s : Fin 4) : Fin 12 := ⟨4 + s.val, by have := s.isLt; omega⟩

/-- 清零相位状态嵌入（0–3 → 8–11）。 -/
def loopResetState (s : Fin 4) : Fin 12 := ⟨8 + s.val, by have := s.isLt; omega⟩

/-- 枚举循环机：加一 ↔ 回块首；溢出则清零并接受。 -/
def enumLoop : DTM 12 where
  step := fun s a =>
    if h : s.val < 4 then
      if s.val = 1 then (4, a, Dir.stay)
      else if s.val = 2 then (8, a, Dir.stay)
      else
        let r := binIncFlag.step ⟨s.val, h⟩ a
        (loopIncState r.1, r.2.1, r.2.2)
    else if h2 : s.val < 8 then
      if s.val = 6 then (0, a, Dir.stay)
      else
        let sB : Fin 4 := ⟨s.val - 4, by omega⟩
        let r := rewindIntoBlock.step sB a
        (loopRewState r.1, r.2.1, r.2.2)
    else if h3 : s.val < 12 then
      let sC : Fin 4 := ⟨s.val - 8, by omega⟩
      let r := resetZeros.step sC a
      (loopResetState r.1, r.2.1, r.2.2)
    else (s, a, Dir.stay)
  start := 0
  accept := 10
  reject := 3

/-- 加一相位照抄 `binIncFlag`（状态 1/2 之外）。 -/
theorem enumLoop_step_inc (s : Fin 4) (a : Sym)
    (h1 : s.val ≠ 1) (h2 : s.val ≠ 2) :
    enumLoop.step (loopIncState s) a
      = (loopIncState (binIncFlag.step s a).1, (binIncFlag.step s a).2) := by
  simp only [enumLoop, loopIncState]
  rw [dite_eq_left s.isLt, ite_eq_right h1, ite_eq_right h2]

/-- 加一相位不终止（排除未用的拒绝状态 3）。 -/
theorem enumLoop_halt_inc (s : Fin 4) (h3 : s.val ≠ 3) :
    enumLoop.accept ≠ loopIncState s ∧ enumLoop.reject ≠ loopIncState s := by
  have hac : ((enumLoop.accept : Fin 12) : Nat) = 10 := rfl
  have hre : ((enumLoop.reject : Fin 12) : Nat) = 3 := rfl
  have hval : ∀ (t : Fin 4), ((loopIncState t : Fin 12) : Nat) = t.val := fun _ => rfl
  constructor
  · intro h
    have := congrArg Fin.val h
    rw [hac, hval] at this
    have := s.isLt
    omega
  · intro h
    have := congrArg Fin.val h
    rw [hre, hval] at this
    exact h3 this.symm

/-- 回块首相位照抄 `rewindIntoBlock`（状态 6 之外）。 -/
theorem enumLoop_step_rewind (s : Fin 4) (a : Sym) (h2 : s.val ≠ 2) :
    enumLoop.step (loopRewState s) a
      = (loopRewState (rewindIntoBlock.step s a).1, (rewindIntoBlock.step s a).2) := by
  simp only [enumLoop, loopRewState]
  rw [dite_eq_right (by omega : ¬ 4 + s.val < 4),
    dite_eq_left (by omega : 4 + s.val < 8),
    ite_eq_right (by omega : ¬ 4 + s.val = 6)]
  have hs : (⟨4 + s.val - 4, by have := s.isLt; omega⟩ : Fin 4) = s :=
    Fin.ext (by simp)
  rw [hs]

/-- 回块首相位不会终止。 -/
theorem enumLoop_halt_rewind (s : Fin 4) :
    enumLoop.accept ≠ loopRewState s ∧ enumLoop.reject ≠ loopRewState s := by
  have hac : ((enumLoop.accept : Fin 12) : Nat) = 10 := rfl
  have hre : ((enumLoop.reject : Fin 12) : Nat) = 3 := rfl
  have hval : ∀ (t : Fin 4), ((loopRewState t : Fin 12) : Nat) = 4 + t.val := fun _ => rfl
  constructor
  · intro h
    have := congrArg Fin.val h
    rw [hac, hval] at this
    have := s.isLt
    omega
  · intro h
    have := congrArg Fin.val h
    rw [hre, hval] at this
    have := s.isLt
    omega

/-- 清零相位照抄 `resetZeros`。 -/
theorem enumLoop_step_reset (s : Fin 4) (a : Sym) :
    enumLoop.step (loopResetState s) a
      = (loopResetState (resetZeros.step s a).1, (resetZeros.step s a).2) := by
  simp only [enumLoop, loopResetState]
  rw [dite_eq_right (by omega : ¬ 8 + s.val < 4),
    dite_eq_right (by omega : ¬ 8 + s.val < 8),
    dite_eq_left (by omega : 8 + s.val < 12)]
  have hs : (⟨8 + s.val - 8, by have := s.isLt; omega⟩ : Fin 4) = s :=
    Fin.ext (by simp)
  rw [hs]

/-- 清零相位不在接受态时的停机判定。 -/
theorem enumLoop_halt_reset (s : Fin 4) (ha : s.val ≠ 2) :
    enumLoop.accept ≠ loopResetState s ∧ enumLoop.reject ≠ loopResetState s := by
  have hac : ((enumLoop.accept : Fin 12) : Nat) = 10 := rfl
  have hre : ((enumLoop.reject : Fin 12) : Nat) = 3 := rfl
  have hval : ∀ (t : Fin 4), ((loopResetState t : Fin 12) : Nat) = 8 + t.val := fun _ => rfl
  constructor
  · intro h
    have := congrArg Fin.val h
    rw [hac, hval] at this
    exact ha (by omega)
  · intro h
    have := congrArg Fin.val h
    rw [hre, hval] at this
    have := s.isLt
    omega

/-- 加一相位在循环机中的整段运行。 -/
theorem enumLoop_embed_inc (n : Nat) (c : Config 4)
    (hnh : ∀ m, m < n → binIncFlag.halted (binIncFlag.run m c) = false)
    (hbad : ∀ m, m < n → (binIncFlag.run m c).state ≠ (2 : Fin 4)) :
    enumLoop.run n { state := loopIncState c.state, tape := c.tape }
      = { state := loopIncState (binIncFlag.run n c).state,
          tape := (binIncFlag.run n c).tape } :=
  run_embed3 binIncFlag enumLoop loopIncState 2
    (fun s a h1 _h3 h2 =>
      enumLoop_step_inc s a (fun hv => h1 (Fin.ext hv))
        (fun hv => h2 (Fin.ext hv)))
    (fun s _h1 h3 _h2 => enumLoop_halt_inc s (fun hv => h3 (Fin.ext hv)))
    n c hnh hbad

/-- 回块首相位在循环机中的整段运行。 -/
theorem enumLoop_embed_rewind (n : Nat) (c : Config 4)
    (hnh : ∀ m, m < n → rewindIntoBlock.halted (rewindIntoBlock.run m c) = false) :
    enumLoop.run n { state := loopRewState c.state, tape := c.tape }
      = { state := loopRewState (rewindIntoBlock.run n c).state,
          tape := (rewindIntoBlock.run n c).tape } :=
  run_embed rewindIntoBlock enumLoop loopRewState
    (fun s a h1 _ => enumLoop_step_rewind s a (fun hv => h1 (Fin.ext hv)))
    (fun s _ _ => enumLoop_halt_rewind s) n c hnh

/-- 清零相位在循环机中的整段运行。 -/
theorem enumLoop_embed_reset (n : Nat) (c : Config 4)
    (hnh : ∀ m, m < n → resetZeros.halted (resetZeros.run m c) = false) :
    enumLoop.run n { state := loopResetState c.state, tape := c.tape }
      = { state := loopResetState (resetZeros.run n c).state,
          tape := (resetZeros.run n c).tape } :=
  run_embed resetZeros enumLoop loopResetState
    (fun s a _ _ => enumLoop_step_reset s a)
    (fun s h1 _ => enumLoop_halt_reset s (fun hv => h1 (Fin.ext hv))) n c hnh

/-- 加一完成后转入回块首相位。 -/
theorem enumLoop_incDone (c : Config 4) (hacc : c.state = binIncFlag.accept) :
    enumLoop.run 1 { state := loopIncState c.state, tape := c.tape }
      = { state := loopRewState 0, tape := (c.tape.write c.tape.read).move Dir.stay } := by
  have hs : c.state.val = 1 := by
    have h := congrArg Fin.val hacc
    simp only [binIncFlag] at h
    exact h
  have hstate1 : loopIncState c.state = (1 : Fin 12) := Fin.ext (by simp [loopIncState, hs])
  have hnh : enumLoop.halted ⟨loopIncState c.state, c.tape⟩ = false := by
    rw [hstate1]
    simp [DTM.halted, enumLoop]
  rw [DTM.run_succ_of_not_halted _ 0 _ hnh]
  simp only [DTM.run, DTM.stepConfig, enumLoop, loopIncState]
  rw [dite_eq_left c.state.isLt, ite_eq_left hs]
  simp [loopRewState]

/-- 回块首完成后回到加一相位，开始下一轮。 -/
theorem enumLoop_rewindDone (c : Config 4) (hacc : c.state = rewindIntoBlock.accept) :
    enumLoop.run 1 { state := loopRewState c.state, tape := c.tape }
      = { state := (0 : Fin 12), tape := (c.tape.write c.tape.read).move Dir.stay } := by
  have hs : c.state.val = 2 := by
    have h := congrArg Fin.val hacc
    simp only [rewindIntoBlock] at h
    exact h
  have hstate6 : loopRewState c.state = (6 : Fin 12) := Fin.ext (by simp [loopRewState, hs])
  have hnh : enumLoop.halted ⟨loopRewState c.state, c.tape⟩ = false := by
    rw [hstate6]
    simp [DTM.halted, enumLoop]
  rw [DTM.run_succ_of_not_halted _ 0 _ hnh]
  simp only [DTM.run, DTM.stepConfig, enumLoop, loopRewState]
  rw [dite_eq_right (by omega : ¬ 4 + c.state.val < 4),
    dite_eq_left (by omega : 4 + c.state.val < 8),
    ite_eq_left (by omega : 4 + c.state.val = 6)]

/-- 加一溢出后转入清零相位。 -/
theorem enumLoop_overflowRoute (c : Config 4) (hov : c.state = (2 : Fin 4)) :
    enumLoop.run 1 { state := loopIncState c.state, tape := c.tape }
      = { state := loopResetState 0, tape := (c.tape.write c.tape.read).move Dir.stay } := by
  have hv : c.state.val = 2 := congrArg Fin.val hov
  have hstate2 : loopIncState c.state = (2 : Fin 12) := Fin.ext (by simp [loopIncState, hv])
  have hnh : enumLoop.halted ⟨loopIncState c.state, c.tape⟩ = false := by
    rw [hstate2]
    simp [DTM.halted, enumLoop]
  rw [DTM.run_succ_of_not_halted _ 0 _ hnh]
  simp only [DTM.run, DTM.stepConfig, enumLoop, loopIncState]
  rw [dite_eq_left c.state.isLt]
  rw [ite_eq_right (by omega : ¬ c.state.val = 1), ite_eq_left hv]
  simp [loopResetState]

/-- 一轮循环（未溢出）：加一 → 回块首 → 回到起点，块前进 1。 -/
theorem enumLoop_round (k : Nat) (rest : List Sym) (hrest : rest ≠ []) :
    enumLoop.run ((k + 1) + 1 + (k + 3) + 1)
      { state := loopIncState 0,
        tape := { left := [], right := List.replicate k (some true) ++ some false :: rest } } =
    { state := (0 : Fin 12),
      tape := { left := [none],
                right := List.replicate k (some false) ++ some true :: rest } } := by
  -- 加一相位的前提
  have hstate0 : ∀ m, m ≤ k →
      (binIncFlag.run m
        { state := (0 : Fin 4),
          tape := { left := [],
                    right := List.replicate k (some true) ++ some false :: rest } }).state = 0 := by
    intro m hm
    rw [binIncFlag_scan_ones [] k m hm (some false :: rest)]
  have hnh : ∀ m, m < k + 1 →
      binIncFlag.halted
        (binIncFlag.run m
          { state := (0 : Fin 4),
            tape := { left := [],
                      right := List.replicate k (some true) ++ some false :: rest } }) = false := by
    intro m hm
    rw [DTM.halted, hstate0 m (by omega)]
    decide
  have hbad : ∀ m, m < k + 1 →
      (binIncFlag.run m
        { state := (0 : Fin 4),
          tape := { left := [],
                    right := List.replicate k (some true) ++ some false :: rest } }).state
        ≠ (2 : Fin 4) := by
    intro m hm
    rw [hstate0 m (by omega)]
    decide
  have hinc := enumLoop_embed_inc (k + 1)
    { state := (0 : Fin 4),
      tape := { left := [], right := List.replicate k (some true) ++ some false :: rest } }
    hnh hbad
  rw [binIncFlag_ones_then_zero [] k rest] at hinc
  simp only [List.append_nil] at hinc
  -- 回块首相位
  have hrew := enumLoop_embed_rewind (k + 3)
    { state := (0 : Fin 4),
      tape := { left := some true :: List.replicate k (some false), right := rest } }
    (rewindIntoBlock_run_nonhalt k rest hrest)
  rw [rewindIntoBlock_run k rest hrest] at hrew
  -- 加一完成 → 回块首相位
  have hsw := enumLoop_incDone
    { state := (1 : Fin 4),
      tape := { left := some true :: List.replicate k (some false), right := rest } }
    rfl
  have htape : ({ left := some true :: List.replicate k (some false), right := rest } : Tape).write
      ({ left := some true :: List.replicate k (some false), right := rest } : Tape).read
      = { left := some true :: List.replicate k (some false), right := rest } :=
    tape_write_read_stay _ (by simpa using hrest)
  rw [htape] at hsw
  simp only [Tape.move] at hsw
  -- 回块首完成 → 回到起点
  have hdone := enumLoop_rewindDone
    { state := (2 : Fin 4),
      tape := { left := [none], right := List.replicate k (some false) ++ some true :: rest } }
    rfl
  have htape2 : ({ left := [none],
                   right := List.replicate k (some false) ++ some true :: rest } : Tape).write
      ({ left := [none],
         right := List.replicate k (some false) ++ some true :: rest } : Tape).read
      = { left := [none], right := List.replicate k (some false) ++ some true :: rest } := by
    apply tape_write_read_stay
    intro h
    have hne : List.replicate k (some false) ++ some true :: rest ≠ [] := by
      cases k with
      | zero => simp
      | succ k => simp [List.replicate_succ]
    exact hne h
  rw [htape2] at hdone
  simp only [Tape.move] at hdone
  -- 拼装
  rw [show (k + 1) + 1 + (k + 3) + 1 = ((k + 1) + (1 + (k + 3))) + 1 by omega,
    DTM.run_add enumLoop ((k + 1) + (1 + (k + 3))) 1,
    DTM.run_add enumLoop (k + 1) (1 + (k + 3)), hinc,
    DTM.run_add enumLoop 1 (k + 3), hsw, hrew, hdone]


/-- 第二轮起的溢出停机：左侧已有一个空白，块全为 1 时加一溢出 → 清零 → 接受。 -/
theorem enumLoop_overflow1 (k : Nat) :
    enumLoop.run ((k + 1) + 1 + (k + 3))
      { state := loopIncState 0,
        tape := { left := [none], right := List.replicate k (some true) ++ [none] } } =
    { state := (10 : Fin 12),
      tape := { left := [none], right := List.replicate (k + 2) (some false) } } := by
  have hstate0 : ∀ m, m ≤ k →
      (binIncFlag.run m
        { state := (0 : Fin 4),
          tape := { left := [none], right := List.replicate k (some true) ++ [none] } }).state = 0 := by
    intro m hm
    rw [binIncFlag_scan_ones [none] k m hm [none]]
  have hnh : ∀ m, m < k + 1 →
      binIncFlag.halted
        (binIncFlag.run m
          { state := (0 : Fin 4),
            tape := { left := [none], right := List.replicate k (some true) ++ [none] } }) = false := by
    intro m hm
    rw [DTM.halted, hstate0 m (by omega)]
    decide
  have hbad : ∀ m, m < k + 1 →
      (binIncFlag.run m
        { state := (0 : Fin 4),
          tape := { left := [none], right := List.replicate k (some true) ++ [none] } }).state
        ≠ (2 : Fin 4) := by
    intro m hm
    rw [hstate0 m (by omega)]
    decide
  have hinc := enumLoop_embed_inc (k + 1)
    { state := (0 : Fin 4),
      tape := { left := [none], right := List.replicate k (some true) ++ [none] } }
    hnh hbad
  rw [binIncFlag_overflow [none] k [none] (Or.inr rfl)] at hinc
  -- 溢出 → 清零相位
  have hroute := enumLoop_overflowRoute
    { state := (2 : Fin 4),
      tape := { left := some true :: (List.replicate k (some false) ++ [none]), right := [] } }
    rfl
  have htape : ({ left := some true :: (List.replicate k (some false) ++ [none]),
                  right := ([] : List Sym) } : Tape).write
      ({ left := some true :: (List.replicate k (some false) ++ [none]),
         right := ([] : List Sym) } : Tape).read
      = { left := some true :: (List.replicate k (some false) ++ [none]), right := [none] } := by
    simp [Tape.read, Tape.write]
  rw [htape] at hroute
  simp only [Tape.move] at hroute
  -- 清零相位（左侧多一个空白）
  have hreset := enumLoop_embed_reset (k + 3)
    { state := (0 : Fin 4),
      tape := { left := some true :: (List.replicate k (some false) ++ [none]), right := [none] } }
    (resetZeros_run1_nonhalt k)
  rw [resetZeros_run1 k] at hreset
  -- 拼装
  rw [show (k + 1) + 1 + (k + 3) = (k + 1) + (1 + (k + 3)) by omega,
    DTM.run_add enumLoop (k + 1) (1 + (k + 3)), hinc,
    DTM.run_add enumLoop 1 (k + 3), hroute, hreset]
  rfl

/-- 一轮循环（第二轮起，左侧已有一个空白）：加一 → 回块首 → 回到起点，块前进 1。 -/
theorem enumLoop_round1 (k : Nat) (rest : List Sym) (hrest : rest ≠ []) :
    enumLoop.run ((k + 1) + 1 + (k + 3) + 1)
      { state := loopIncState 0,
        tape := { left := [none], right := List.replicate k (some true) ++ some false :: rest } } =
    { state := (0 : Fin 12),
      tape := { left := [none],
                right := List.replicate k (some false) ++ some true :: rest } } := by
  -- 加一相位的前提
  have hstate0 : ∀ m, m ≤ k →
      (binIncFlag.run m
        { state := (0 : Fin 4),
          tape := { left := [none],
                    right := List.replicate k (some true) ++ some false :: rest } }).state = 0 := by
    intro m hm
    rw [binIncFlag_scan_ones [none] k m hm (some false :: rest)]
  have hnh : ∀ m, m < k + 1 →
      binIncFlag.halted
        (binIncFlag.run m
          { state := (0 : Fin 4),
            tape := { left := [none],
                      right := List.replicate k (some true) ++ some false :: rest } }) = false := by
    intro m hm
    rw [DTM.halted, hstate0 m (by omega)]
    decide
  have hbad : ∀ m, m < k + 1 →
      (binIncFlag.run m
        { state := (0 : Fin 4),
          tape := { left := [none],
                    right := List.replicate k (some true) ++ some false :: rest } }).state
        ≠ (2 : Fin 4) := by
    intro m hm
    rw [hstate0 m (by omega)]
    decide
  have hinc := enumLoop_embed_inc (k + 1)
    { state := (0 : Fin 4),
      tape := { left := [none], right := List.replicate k (some true) ++ some false :: rest } }
    hnh hbad
  rw [binIncFlag_ones_then_zero [none] k rest] at hinc
  -- 回块首相位（左侧多一个空白）
  have hrew := enumLoop_embed_rewind (k + 3)
    { state := (0 : Fin 4),
      tape := { left := some true :: (List.replicate k (some false) ++ [none]), right := rest } }
    (rewindIntoBlock_run1_nonhalt k rest hrest)
  rw [rewindIntoBlock_run1 k rest hrest] at hrew
  -- 加一完成 → 回块首相位
  have hsw := enumLoop_incDone
    { state := (1 : Fin 4),
      tape := { left := some true :: (List.replicate k (some false) ++ [none]), right := rest } }
    rfl
  have htape : ({ left := some true :: (List.replicate k (some false) ++ [none]),
                  right := rest } : Tape).write
      ({ left := some true :: (List.replicate k (some false) ++ [none]), right := rest } : Tape).read
      = { left := some true :: (List.replicate k (some false) ++ [none]), right := rest } :=
    tape_write_read_stay _ (by simpa using hrest)
  rw [htape] at hsw
  simp only [Tape.move] at hsw
  -- 回块首完成 → 回到起点
  have hdone := enumLoop_rewindDone
    { state := (2 : Fin 4),
      tape := { left := [none], right := List.replicate k (some false) ++ some true :: rest } }
    rfl
  have htape2 : ({ left := [none],
                   right := List.replicate k (some false) ++ some true :: rest } : Tape).write
      ({ left := [none],
         right := List.replicate k (some false) ++ some true :: rest } : Tape).read
      = { left := [none], right := List.replicate k (some false) ++ some true :: rest } := by
    apply tape_write_read_stay
    intro h
    have hne : List.replicate k (some false) ++ some true :: rest ≠ [] := by
      cases k with
      | zero => simp
      | succ k => simp [List.replicate_succ]
    exact hne h
  rw [htape2] at hdone
  simp only [Tape.move] at hdone
  -- 拼装
  rw [show (k + 1) + 1 + (k + 3) + 1 = ((k + 1) + (1 + (k + 3))) + 1 by omega,
    DTM.run_add enumLoop ((k + 1) + (1 + (k + 3))) 1,
    DTM.run_add enumLoop (k + 1) (1 + (k + 3)), hinc,
    DTM.run_add enumLoop 1 (k + 3), hsw, hrew, hdone]

/-- 溢出停机：整块全是 1 时，加一溢出 → 清零 → 接受。 -/
theorem enumLoop_overflow (k : Nat) (e : List Sym) (he : e = [] ∨ e = [none]) :
    enumLoop.run ((k + 1) + 1 + (k + 3))
      { state := loopIncState 0,
        tape := { left := [], right := List.replicate k (some true) ++ e } } =
    { state := (10 : Fin 12),
      tape := { left := [none], right := List.replicate (k + 2) (some false) } } := by
  have hstate0 : ∀ m, m ≤ k →
      (binIncFlag.run m
        { state := (0 : Fin 4),
          tape := { left := [], right := List.replicate k (some true) ++ e } }).state = 0 := by
    intro m hm
    rw [binIncFlag_scan_ones [] k m hm e]
  have hnh : ∀ m, m < k + 1 →
      binIncFlag.halted
        (binIncFlag.run m
          { state := (0 : Fin 4),
            tape := { left := [], right := List.replicate k (some true) ++ e } }) = false := by
    intro m hm
    rw [DTM.halted, hstate0 m (by omega)]
    decide
  have hbad : ∀ m, m < k + 1 →
      (binIncFlag.run m
        { state := (0 : Fin 4),
          tape := { left := [], right := List.replicate k (some true) ++ e } }).state
        ≠ (2 : Fin 4) := by
    intro m hm
    rw [hstate0 m (by omega)]
    decide
  have hinc := enumLoop_embed_inc (k + 1)
    { state := (0 : Fin 4),
      tape := { left := [], right := List.replicate k (some true) ++ e } }
    hnh hbad
  rw [binIncFlag_overflow [] k e he] at hinc
  simp only [List.append_nil] at hinc
  -- 溢出 → 清零相位
  have hroute := enumLoop_overflowRoute
    { state := (2 : Fin 4),
      tape := { left := some true :: List.replicate k (some false), right := [] } }
    rfl
  have htape : ({ left := some true :: List.replicate k (some false), right := [] } : Tape).write
      ({ left := some true :: List.replicate k (some false), right := [] } : Tape).read
      = { left := some true :: List.replicate k (some false), right := [none] } := by
    simp [Tape.read, Tape.write]
  rw [htape] at hroute
  simp only [Tape.move] at hroute
  -- 清零相位
  have hreset := enumLoop_embed_reset (k + 3)
    { state := (0 : Fin 4),
      tape := { left := some true :: List.replicate k (some false), right := [none] } }
    (resetZeros_run_nonhalt k [none] (Or.inr rfl))
  rw [resetZeros_run k [none] (Or.inr rfl)] at hreset
  -- 拼装
  rw [show (k + 1) + 1 + (k + 3) = (k + 1) + (1 + (k + 3)) by omega,
    DTM.run_add enumLoop (k + 1) (1 + (k + 3)), hinc,
    DTM.run_add enumLoop 1 (k + 3), hroute, hreset]
  rfl

end DTM

end Pnp
