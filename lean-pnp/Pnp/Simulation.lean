/-
  文件：Pnp/Simulation.lean
  主题：接受语义与「枚举所有分支」的等价关系（B5 阶段 2.5）。

  内容：
    - `usedPrefix`：一条成功运行实际消耗掉的选择前缀（停机或失败时停止）；
    - `runWith_usedPrefix`：用该前缀（恰好它的长度步）重跑，得到同一结果；
    - 前缀长度不超过预算 T，且其中每个编号都小于分支上界 B；
    - 主定理 `acceptsWithin_allSeqs`：非确定机在 T 步内接受，
      当且仅当在 `allSeqs B T` 中存在一条长度恰为 T 的序列，模拟后停在接受状态。

  这一步把「枚举分支」的语义正确性钉死；阶段 3（把枚举实现成单带图灵机）
  仍未完成，因此**不能**据此声明 NP ⊆ EXP。
-/

import Pnp.Classes
import Pnp.Enumeration
import Pnp.Branching

namespace Pnp

/-- `pick l i = some a` 说明下标 `i` 在表长范围内。 -/
theorem pick_some_lt {α : Type} :
    ∀ (l : List α) (i : Nat) (a : α), pick l i = some a → i < l.length
  | [], i, a, h => by simp [pick] at h
  | _ :: _, 0, a, _ => by simp
  | _ :: l, i + 1, a, h => by
      simp only [pick] at h
      exact Nat.succ_lt_succ (pick_some_lt l i a h)

namespace NTM

variable {q : Nat}

/-- 成功走一步时，所用的候选编号小于该步的候选列表长度。 -/
theorem lt_step_length_of_stepWith (M : NTM q) (c : Config q) (i : Nat) (c' : Config q)
    (h : M.stepWith c i = some c') :
    i < (M.step c.state c.tape.read).length := by
  unfold stepWith at h
  cases hp : pick (M.step c.state c.tape.read) i with
  | none => simp [hp] at h
  | some x => exact pick_some_lt _ _ _ hp

/-- 一条运行实际消耗掉的选择前缀（停机、无选择或越界时停止）。 -/
def usedPrefix (M : NTM q) : Nat → List Nat → Config q → List Nat
  | 0, _, _ => []
  | n + 1, choices, c =>
      match M.halted c with
      | true => []
      | false =>
          match choices with
          | [] => []
          | i :: rest =>
              match M.stepWith c i with
              | none => []
              | some c' => i :: M.usedPrefix n rest c'

/-- `usedPrefix` 在步数非零时的展开式（便于定向改写）。 -/
theorem usedPrefix_succ (M : NTM q) (n : Nat) (choices : List Nat) (c : Config q) :
    M.usedPrefix (Nat.succ n) choices c =
      (match M.halted c with
       | true => []
       | false =>
           match choices with
           | [] => []
           | i :: rest =>
               match M.stepWith c i with
               | none => []
               | some c' => i :: M.usedPrefix n rest c') := by
  cases choices <;> rfl

/-- 消耗的前缀长度不超过预算步数。 -/
theorem usedPrefix_length_le (M : NTM q) (T : Nat) (choices : List Nat) (c : Config q) :
    (M.usedPrefix T choices c).length ≤ T := by
  induction T generalizing choices c with
  | zero => simp [usedPrefix]
  | succ T ih =>
      rw [usedPrefix_succ]
      cases hc : M.halted c with
      | true =>
          simp only [List.length_nil]
          omega
      | false =>
          cases choices with
          | nil =>
              simp only [List.length_nil]
              omega
          | cons i rest =>
              cases hs : M.stepWith c i with
              | none =>
                  simp only [hs, List.length_nil]
                  omega
              | some c' =>
                  simp only [hs, List.length_cons]
                  have := ih rest c'
                  omega

/-- 用消耗前缀重跑：结果与原来完全一致。 -/
theorem runWith_usedPrefix (M : NTM q) :
    ∀ (T : Nat) (choices : List Nat) (c c' : Config q),
      M.runWith T choices c = some c' →
      M.runWith (M.usedPrefix T choices c).length (M.usedPrefix T choices c) c = some c' := by
  intro T
  induction T with
  | zero =>
      intro choices c c' h
      simp only [NTM.runWith, Option.some.injEq] at h
      subst h
      simp [usedPrefix, NTM.runWith]
  | succ T ih =>
      intro choices c c' h
      rw [runWith_succ] at h
      rw [usedPrefix_succ]
      cases hc : M.halted c with
      | true =>
          simp only [hc, Option.some.injEq] at h
          subst h
          simp [NTM.runWith]
      | false =>
          simp only [hc] at h
          cases choices with
          | nil => cases h
          | cons i rest =>
              cases hs : M.stepWith c i with
              | none =>
                  simp only [hs] at h
                  cases h
              | some c'' =>
                  simp only [hs, Option.bind_some] at h
                  -- 目标化简为「先走 i，再用剩余前缀」
                  simp only [hs, List.length_cons]
                  have hpre := ih rest c'' c' h
                  -- 把步数写成后继形式，展开一步
                  show M.runWith (Nat.succ (M.usedPrefix T rest c'').length)
                      (i :: M.usedPrefix T rest c'') c = some c'
                  rw [runWith_succ]
                  simp only [hc, hs, Option.bind_some]
                  exact hpre

/-- 前缀里的每个编号都小于分支上界。 -/
theorem usedPrefix_lt_bound (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) :
    ∀ (T : Nat) (choices : List Nat) (c : Config q) (x : Nat),
      x ∈ M.usedPrefix T choices c → x < B := by
  intro T
  induction T with
  | zero =>
      intro choices c x hx
      simp only [usedPrefix] at hx
      simp at hx
  | succ T ih =>
      intro choices c x hx
      rw [usedPrefix_succ] at hx
      cases hc : M.halted c with
      | true =>
          simp only [hc] at hx
          simp at hx
      | false =>
          simp only [hc] at hx
          cases choices with
          | nil => simp at hx
          | cons i rest =>
              cases hs : M.stepWith c i with
              | none =>
                  simp only [hs] at hx
                  simp at hx
              | some c'' =>
                  simp only [hs, List.mem_cons] at hx
                  rcases hx with rfl | hx
                  · -- 消耗的编号 i 小于候选表长，而表长 ≤ B
                    exact Nat.lt_of_lt_of_le
                      (lt_step_length_of_stepWith M _ _ _ hs) (hB _ _)
                  · exact ih rest c'' x hx

end NTM

/-- 主定理：T 步内接受 ⇔ 在 `allSeqs B T` 中存在一条模拟到接受的序列。 -/
theorem acceptsWithin_allSeqs {q : Nat} {M : NTM q} {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B) :
    ∀ (w : List Bool) (T : Nat),
      M.AcceptsWithin w T ↔
        ∃ cs ∈ allSeqs B T, ∃ c : Config q,
          M.runWith T cs (M.init w) = some c ∧ c.state = M.accept := by
  intro w T
  constructor
  · -- 接受 ⇒ 取实际消耗的前缀，补零到长度 T
    rintro ⟨choices, hlen, c, hrun, hstate⟩
    have hup_len : (M.usedPrefix T choices (M.init w)).length ≤ T :=
      NTM.usedPrefix_length_le M T choices (M.init w)
    have hup_run : M.runWith (M.usedPrefix T choices (M.init w)).length
        (M.usedPrefix T choices (M.init w)) (M.init w) = some c :=
      NTM.runWith_usedPrefix M T choices (M.init w) c hrun
    have hhalt : M.halted c = true :=
      NTM.halted_of_state M c (Or.inl hstate)
    -- 停机后补零不改变结果
    have hext : M.runWith T
        (M.usedPrefix T choices (M.init w) ++ List.replicate (T - (M.usedPrefix T choices (M.init w)).length) 0)
        (M.init w) = some c :=
      NTM.runWith_extend M (M.usedPrefix T choices (M.init w)).length
        (M.usedPrefix T choices (M.init w)) (M.init w) c
        hup_run hhalt T (List.replicate (T - (M.usedPrefix T choices (M.init w)).length) 0)
        hup_len
    refine ⟨M.usedPrefix T choices (M.init w) ++
        List.replicate (T - (M.usedPrefix T choices (M.init w)).length) 0, ?_, c, hext, hstate⟩
    rw [mem_allSeqs]
    constructor
    · -- 长度恰为 T
      simp only [List.length_append, List.length_replicate]
      omega
    · -- 前缀编号 < B，补零段为 0 < B
      intro x hx
      rw [List.mem_append] at hx
      rcases hx with hx | hx
      · exact NTM.usedPrefix_lt_bound M hB T choices (M.init w) x hx
      · rw [List.eq_of_mem_replicate hx]
        exact hBpos
  · -- 枚举中的序列本身就是一条接受分支
    rintro ⟨cs, hcs, c, hrun, hstate⟩
    have hlen : cs.length = T := (mem_allSeqs.mp hcs).1
    exact ⟨cs, by omega, c, hrun, hstate⟩

end Pnp
