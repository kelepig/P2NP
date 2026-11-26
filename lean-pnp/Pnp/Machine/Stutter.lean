/-
  文件：Pnp/Machine/Stutter.lean
  主题：占位转移（stutter）——给每个状态-符号的候选转移表头部加一个「原地不动」的动作，
        使选择索引整体后移一位。

  为什么需要它（auto-run-log #113 记录）：通路模拟器 `passRun` 的数字区语义是
  「块值 `k` ⇒ 下一轮选择编号为 `k + 1`」（SimPass 文件头），因此它能模拟的选择序列
  除首个之外都必须 ≥ 1；而下标枚举 `seqOfIndex` 产生 [0, B) 内的任意序列，含 0。
  解决办法：让外层枚举模拟 `M.stutter`——索引 0 是「原地空转一步」，索引 `c+1` 恰为
  原机索引 `c`。于是
    - 原机接受 ⇒ 占位机接受（选择索引整体 +1，全部 ≥ 1，可被通路模拟）；
    - 占位机接受 ⇒ 原机接受（删掉空转步，步数与选择数都不增）。

  注意：空转步「写入读到的符号 + 原地不动」在右侧为空时会把纸带右端补一个空白格，
  故它不是逐字不变，而是「语义不变」（`Tape.SameInf`）；删空转步时用
  `NTM.runWith_sameInf` 把空白差异吸收掉。

  Stutter padding: prepending a no-op transition makes index 0 a stuttering step and
  index `c+1` the original choice `c`.  This aligns `seqOfIndex`'s [0, B) sequences
  with the pass machinery's "next choice = digit + 1" convention (auto-run-log #113).
  The stuttering step preserves the tape only up to trailing blanks (`SameInf`).
-/

import Pnp.Machine.PadInv

namespace Pnp

namespace Tape

/-- 写入当前读到的符号是语义恒等：右侧为空时只多出一个空白格。
    Writing back the read symbol is the identity up to trailing blanks. -/
theorem write_read_sameInf (t : Tape) : SameInf (t.write t.read) t := by
  cases t with
  | mk l r =>
    cases r with
    | nil =>
        exact ⟨0, 1, by simp [write], by simp [write, read]⟩
    | cons x xs =>
        have hne : (Tape.mk l (x :: xs)).right ≠ [] := by simp
        rw [write_read _ hne]
        exact sameInf_refl _

end Tape

namespace NTM

/-- 占位机：每个候选表头部加一个「原地不动」的转移。
    Stutter machine: prepend a stay-put transition to each candidate list. -/
def stutter (M : NTM q) : NTM q where
  step := fun s a => (s, a, Dir.stay) :: M.step s a
  start := M.start
  accept := M.accept
  reject := M.reject

/-- 占位机的停机判断与原机一致。 -/
theorem stutter_halted (M : NTM q) (c : Config q) :
    (M.stutter).halted c = M.halted c := rfl

/-- 索引 `c+1` 等价于原机的索引 `c`。 -/
theorem stutter_stepWith_succ (M : NTM q) (c : Config q) (i : Nat) :
    (M.stutter).stepWith c (i + 1) = M.stepWith c i := by
  simp only [stepWith, stutter]
  rfl

/-- 索引 0 是空转：状态不变，纸带只差两端空白。
    Index 0 stutters: same state, tape unchanged up to trailing blanks. -/
theorem stutter_stepWith_zero_sameInf (M : NTM q) (c : Config q) :
    ∃ c', (M.stutter).stepWith c 0 = some c' ∧ c'.state = c.state ∧
      Tape.SameInf c'.tape c.tape := by
  refine ⟨{ state := c.state, tape := (c.tape.write c.tape.read).move Dir.stay },
    ?_, rfl, ?_⟩
  · -- 取第 0 个候选：恰好是刚加的「原地不动」转移
    simp only [stepWith, stutter]
    rfl
  · -- 空转 = 写回读到的符号 + 原地不动
    exact Tape.write_read_sameInf c.tape

/-- 占位机的分支数上限只增加 1。 -/
theorem stutter_step_length (M : NTM q) (B : Nat)
    (hB : ∀ s a, (M.step s a).length ≤ B) (s : Fin q) (a : Sym) :
    ((M.stutter).step s a).length ≤ B + 1 := by
  have h : ((M.stutter).step s a).length = (M.step s a).length + 1 := rfl
  have := hB s a
  omega

/-- 选择索引整体 +1 后，占位机的运行与原机一致。 -/
theorem stutter_runWith (M : NTM q) :
    ∀ (T : Nat) (cs : List Nat) (x : Config q),
      (M.stutter).runWith T (cs.map (· + 1)) x = M.runWith T cs x := by
  intro T
  induction T with
  | zero => intro cs x; rfl
  | succ T ih =>
      intro cs x
      rw [runWith_succ, runWith_succ, stutter_halted]
      cases hh : M.halted x with
      | true => rfl
      | false =>
          cases cs with
          | nil => rfl
          | cons i rest =>
              simp only [List.map_cons, stutter_stepWith_succ]
              cases hs : M.stepWith x i with
              | none => rfl
              | some x' => exact ih rest x'

/-- **原机接受 ⇒ 占位机接受**：选择索引整体 +1（全部 ≥ 1，可被通路数字区模拟）。 -/
theorem acceptsWithin_stutter (M : NTM q) (w : List Bool) (T : Nat)
    (h : M.AcceptsWithin w T) : (M.stutter).AcceptsWithin w T := by
  obtain ⟨cs, hlen, c, hrun, hacc⟩ := h
  refine ⟨cs.map (· + 1), ?_, c, ?_, hacc⟩
  · rw [List.length_map]
    exact hlen
  · rw [stutter_runWith]
    exact hrun

/-- 未停机时展开一步：`runWith (T+1) (j :: cs) x = (stepWith x j).bind …`。
    Unfolding one step when `x` has not halted. -/
theorem runWith_succ_cons (M : NTM q) (T j : Nat) (cs : List Nat) (x : Config q)
    (hh : M.halted x = false) :
    M.runWith (T + 1) (j :: cs) x =
      (M.stepWith x j).bind (fun c' => M.runWith T cs c') := by
  rw [runWith_succ, hh]

/-- 占位机的一条运行可整理为原机运行：删掉空转步，步数与选择数都不增加。
    A stutter run compresses into an original run of no greater length. -/
theorem exists_run_of_stutter (M : NTM q) :
    ∀ (T : Nat) (cs : List Nat) (x y : Config q),
      (M.stutter).runWith T cs x = some y → y.state = M.accept →
      ∃ (T' : Nat) (cs' : List Nat) (y' : Config q),
        T' ≤ T ∧ cs'.length ≤ T' ∧ M.runWith T' cs' x = some y' ∧ y'.state = M.accept := by
  intro T
  induction T with
  | zero =>
      intro cs x y h hacc
      simp only [runWith, Option.some.injEq] at h
      subst h
      exact ⟨0, [], x, by omega, by simp, rfl, hacc⟩
  | succ T ih =>
      intro cs x y h hacc
      rw [runWith_succ] at h
      cases hh : (M.stutter).halted x with
      | true =>
          simp only [hh, Option.some.injEq] at h
          subst h
          exact ⟨0, [], x, by omega, by simp, rfl, hacc⟩
      | false =>
          have hhM : M.halted x = false := by rw [stutter_halted] at hh; exact hh
          simp only [hh] at h
          cases cs with
          | nil =>
              simp only at h
              cases h
          | cons i rest =>
              simp only at h
              cases i with
              | zero =>
                  -- 空转一步：起点换成原机（纸带只差两端空白），不占步数
                  obtain ⟨x1, hstep0, hstate0, hsame0⟩ := stutter_stepWith_zero_sameInf M x
                  rw [hstep0] at h
                  have h' : (M.stutter).runWith T rest x1 = some y := h
                  obtain ⟨T', cs', y', hT', hlen', hrun', hacc'⟩ := ih rest x1 y h' hacc
                  obtain ⟨y'', hrun'', hstate'', -⟩ :=
                    runWith_sameInf M T' cs' x1 x hstate0 hsame0 y' hrun'
                  exact ⟨T', cs', y'', by omega, hlen', hrun'',
                    by rw [← hstate'']; exact hacc'⟩
              | succ j =>
                  -- 真实一步：换成原机索引 `j`
                  rw [stutter_stepWith_succ] at h
                  cases hstep : M.stepWith x j with
                  | none =>
                      rw [hstep] at h
                      have h2 : (none : Option (Config q)) = some y := h
                      cases h2
                  | some x' =>
                      rw [hstep] at h
                      have h' : (M.stutter).runWith T rest x' = some y := h
                      obtain ⟨T', cs', y', hT', hlen', hrun', hacc'⟩ := ih rest x' y h' hacc
                      refine ⟨T' + 1, j :: cs', y', by omega, ?_, ?_, hacc'⟩
                      · simp only [List.length_cons]
                        omega
                      · rw [runWith_succ_cons M T' j cs' x hhM, hstep]
                        exact hrun'

/-- **占位机接受 ⇒ 原机接受**：删去空转步，步数不超过原预算。 -/
theorem acceptsWithin_of_stutter (M : NTM q) (w : List Bool) (T : Nat)
    (h : (M.stutter).AcceptsWithin w T) : M.AcceptsWithin w T := by
  obtain ⟨cs, hlen, c, hrun, hacc⟩ := h
  have hinit : (M.stutter).init w = M.init w := rfl
  rw [hinit] at hrun
  obtain ⟨T', cs', y', hT', hlen', hrun', hacc'⟩ :=
    exists_run_of_stutter M T cs (M.init w) c hrun hacc
  have hhalt : M.halted y' = true := halted_of_state M y' (Or.inl hacc')
  refine ⟨cs' ++ [], ?_, y', ?_, hacc'⟩
  · rw [List.length_append, List.length_nil]
    omega
  · have := runWith_extend M T' cs' (M.init w) y' hrun' hhalt T [] hT'
    exact this

/-- 两个方向合起来：占位机与原机的接受能力等价（同一时间预算）。 -/
theorem acceptsWithin_stutter_iff (M : NTM q) (w : List Bool) (T : Nat) :
    (M.stutter).AcceptsWithin w T ↔ M.AcceptsWithin w T :=
  ⟨acceptsWithin_of_stutter M w T, acceptsWithin_stutter M w T⟩

end NTM

end Pnp
