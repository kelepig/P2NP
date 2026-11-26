/-
  文件：Pnp/Machine/EnumRound.lean
  主题：枚举循环的一轮合并机 `enumRound`。

  状态布局（共 10 个状态）：
    - 0–3：`binIncFlag` 加一相位（0 扫描，1 正常完成，2 溢出，3 未用）；
    - 4–7：`rewindIntoBlock` 回块首相位（4 跨入，5 扫描，6 接受，7 拒绝）。

  路由：
    - 加一正常完成（状态 1）→ 原地转入回块首相位（状态 4）；
    - 加一溢出（状态 2）→ 进入拒绝状态 9（溢出分支由外层循环另行处理）；
    - 回块首接受（状态 6）→ 即合并机接受状态，整个一轮结束。

  本文件证明一轮的完整运行：
    从「块 = `true^k ++ false :: rest`、头在块首」出发，
    `(k+1) + 1 + (k+3)` 步后块变成 `false^k ++ true :: rest`、头回到块首。
-/

import Pnp.Machine.IncFlag
import Pnp.Machine.Scan
import Pnp.Machine.Embed

namespace Pnp

namespace DTM

/-- 加一相位状态嵌入到合并机（0–3 → 0–3）。 -/
def incState (s : Fin 4) : Fin 10 := ⟨s.val, by have := s.isLt; omega⟩

/-- 回块首相位状态嵌入到合并机（0–3 → 4–7）。 -/
def rewState (s : Fin 4) : Fin 10 := ⟨4 + s.val, by have := s.isLt; omega⟩

/-- 一轮合并机：加一 → 回块首。 -/
def enumRound : DTM 10 where
  step := fun s a =>
    if h : s.val < 4 then
      if s.val = 1 then (4, a, Dir.stay)
      else if s.val = 2 then (9, a, Dir.stay)
      else
        let r := binIncFlag.step ⟨s.val, h⟩ a
        (incState r.1, r.2.1, r.2.2)
    else if h2 : s.val < 8 then
      if s.val = 6 then (s, a, Dir.stay)
      else
        let sB : Fin 4 := ⟨s.val - 4, by omega⟩
        let r := rewindIntoBlock.step sB a
        (rewState r.1, r.2.1, r.2.2)
    else (s, a, Dir.stay)
  start := 0
  accept := 6
  reject := 9

/-- 加一相位的转移与 `binIncFlag` 一致（状态 1/2 之外照抄）。 -/
theorem enumRound_step_inc (s : Fin 4) (a : Sym)
    (h1 : s.val ≠ 1) (h2 : s.val ≠ 2) :
    enumRound.step (incState s) a
      = (incState (binIncFlag.step s a).1, (binIncFlag.step s a).2) := by
  simp only [enumRound, incState]
  rw [dite_eq_left s.isLt]
  rw [ite_eq_right h1, ite_eq_right h2]

/-- 加一相位不会落入合并机的接受/拒绝状态。 -/
theorem enumRound_halt_inc (s : Fin 4) :
    enumRound.accept ≠ incState s ∧ enumRound.reject ≠ incState s := by
  constructor
  · intro h
    have hv : ((6 : Fin 10) : Nat) = ((incState s) : Nat) := by
      simpa only [enumRound] using congrArg Fin.val h
    simp only [incState] at hv
    have := s.isLt
    omega
  · intro h
    have hv : ((9 : Fin 10) : Nat) = ((incState s) : Nat) := by
      simpa only [enumRound] using congrArg Fin.val h
    simp only [incState] at hv
    have := s.isLt
    omega

/-- 回块首相位的转移与 `rewindIntoBlock` 一致。 -/
theorem enumRound_step_rewind (s : Fin 4) (a : Sym) (h2 : s.val ≠ 2) :
    enumRound.step (rewState s) a
      = (rewState (rewindIntoBlock.step s a).1, (rewindIntoBlock.step s a).2) := by
  simp only [enumRound, rewState]
  rw [dite_eq_right (by omega : ¬ 4 + s.val < 4),
    dite_eq_left (by omega : 4 + s.val < 8),
    ite_eq_right (by omega : ¬ 4 + s.val = 6)]
  have hs : (⟨4 + s.val - 4, by have := s.isLt; omega⟩ : Fin 4) = s :=
    Fin.ext (by simp)
  rw [hs]

/-- 回块首相位不会落入合并机的接受/拒绝状态。 -/
theorem enumRound_halt_rewind (s : Fin 4) (ha : s ≠ rewindIntoBlock.accept) :
    enumRound.accept ≠ rewState s ∧ enumRound.reject ≠ rewState s := by
  have haccVal : ((enumRound.accept : Fin 10) : Nat) = 6 := rfl
  have hrejVal : ((enumRound.reject : Fin 10) : Nat) = 9 := rfl
  have hrewVal : ∀ (t : Fin 4), ((rewState t : Fin 10) : Nat) = 4 + t.val := fun _ => rfl
  constructor
  · intro h
    have h3 := congrArg Fin.val h
    rw [haccVal, hrewVal] at h3
    have hs2 : s.val = 2 := by omega
    exact ha (by rw [show rewindIntoBlock.accept = (2 : Fin 4) from rfl]; exact Fin.ext hs2)
  · intro h
    have h3 := congrArg Fin.val h
    rw [hrejVal, hrewVal] at h3
    have := s.isLt
    omega

/-- 加一相位在合并机中的整段运行。 -/
theorem enumRound_embed_inc (n : Nat) (c : Config 4)
    (hnh : ∀ m, m < n → binIncFlag.halted (binIncFlag.run m c) = false)
    (hbad : ∀ m, m < n → (binIncFlag.run m c).state ≠ (2 : Fin 4)) :
    enumRound.run n { state := incState c.state, tape := c.tape }
      = { state := incState (binIncFlag.run n c).state,
          tape := (binIncFlag.run n c).tape } :=
  run_embed3 binIncFlag enumRound incState 2
    (fun s a h1 _ h3 =>
      enumRound_step_inc s a (fun hv => h1 (Fin.ext hv)) (fun hv => h3 (Fin.ext hv)))
    (fun s _ _ _ => enumRound_halt_inc s) n c hnh hbad

/-- 回块首相位在合并机中的整段运行。 -/
theorem enumRound_embed_rewind (n : Nat) (c : Config 4)
    (hnh : ∀ m, m < n → rewindIntoBlock.halted (rewindIntoBlock.run m c) = false) :
    enumRound.run n { state := rewState c.state, tape := c.tape }
      = { state := rewState (rewindIntoBlock.run n c).state,
          tape := (rewindIntoBlock.run n c).tape } :=
  run_embed rewindIntoBlock enumRound rewState
    (fun s a h1 _ => enumRound_step_rewind s a (fun hv => h1 (Fin.ext hv)))
    (fun s ha _ => enumRound_halt_rewind s ha) n c hnh

/-- 切换步：加一接受后原地转入回块首相位。 -/
theorem enumRound_switch (c : Config 4) (hacc : c.state = binIncFlag.accept) :
    enumRound.run 1 { state := incState c.state, tape := c.tape }
      = { state := rewState 0, tape := (c.tape.write c.tape.read).move Dir.stay } := by
  have hs : c.state.val = 1 := by
    have h := congrArg Fin.val hacc
    simp only [binIncFlag] at h
    exact h
  have hstate1 : incState c.state = (1 : Fin 10) := Fin.ext (by simp [incState, hs])
  have hnh : enumRound.halted ⟨incState c.state, c.tape⟩ = false := by
    rw [hstate1]
    simp [DTM.halted, enumRound]
  rw [DTM.run_succ_of_not_halted _ 0 _ hnh]
  simp only [DTM.run, DTM.stepConfig, enumRound, incState]
  rw [dite_eq_left c.state.isLt, ite_eq_left hs]
  simp [rewState]

/-- 纸带右侧非空时，「写回读到的符号 + 原地不动」不改变纸带。 -/
theorem tape_write_read_stay (t : Tape) (h : t.right ≠ []) :
    (t.write t.read).move Dir.stay = t := by
  rcases t with ⟨l, r⟩
  rcases r with _ | ⟨x, xs⟩
  · exact absurd rfl h
  · simp [Tape.read, Tape.write, Tape.move]

/-- 一轮枚举：加一成功 + 回块首，步数 `(k+1) + 1 + (k+3)`。 -/
theorem enumRound_round (k : Nat) (rest : List Sym) (hrest : rest ≠ []) :
    enumRound.run ((k + 1) + 1 + (k + 3))
      { state := incState 0,
        tape := { left := [], right := List.replicate k (some true) ++ some false :: rest } } =
    { state := rewState 2,
      tape := { left := [none],
                right := List.replicate k (some false) ++ some true :: rest } } := by
  -- 加一相位的两个前提：前缀不停机、且不经过溢出状态 2
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
                    right := List.replicate k (some true) ++ some false :: rest } }).state ≠ (2 : Fin 4) := by
    intro m hm
    rw [hstate0 m (by omega)]
    decide
  -- 加一相位结束后的格局
  have hinc := enumRound_embed_inc (k + 1)
    { state := (0 : Fin 4),
      tape := { left := [], right := List.replicate k (some true) ++ some false :: rest } }
    hnh hbad
  rw [binIncFlag_ones_then_zero [] k rest] at hinc
  simp only [List.append_nil] at hinc
  -- 回块首相位的前提
  have hnh2 : ∀ m, m < k + 3 →
      rewindIntoBlock.halted
        (rewindIntoBlock.run m
          { state := (0 : Fin 4),
            tape := { left := some true :: List.replicate k (some false), right := rest } }) = false :=
    rewindIntoBlock_run_nonhalt k rest hrest
  have hrew := enumRound_embed_rewind (k + 3)
    { state := (0 : Fin 4),
      tape := { left := some true :: List.replicate k (some false), right := rest } }
    hnh2
  rw [rewindIntoBlock_run k rest hrest] at hrew
  -- 切换步（写回读到的符号后原地不动，纸带不变）
  have hsw := enumRound_switch
    { state := (1 : Fin 4),
      tape := { left := some true :: List.replicate k (some false), right := rest } }
    rfl
  have htape : ({ left := some true :: List.replicate k (some false), right := rest } : Tape).write
      ({ left := some true :: List.replicate k (some false), right := rest } : Tape).read
      = { left := some true :: List.replicate k (some false), right := rest } :=
    tape_write_read_stay _ (by simpa using hrest)
  rw [htape] at hsw
  simp only [Tape.move] at hsw
  -- 拼装：加一 → 切换 → 回块首
  rw [show (k + 1) + 1 + (k + 3) = (k + 1) + (1 + (k + 3)) by omega,
    DTM.run_add enumRound (k + 1) (1 + (k + 3)), hinc,
    DTM.run_add enumRound 1 (k + 3), hsw, hrew]

end DTM

end Pnp
