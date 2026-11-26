/-
  文件：Pnp/Classes.lean
  主题：时间受限判定器、P 与 NP 的正式定义。

  设计取舍（务必与 docs/04 一起读）：
    - P 用确定性图灵机定义：存在多项式时间上限的判定器。
    - NP 用非确定性图灵机定义：存在多项式时间上限、能在某条分支上接受的机器。
      这与「证书验证器」定义等价，但该等价本身需要另行证明（后续任务）。
      先选非确定机，是因为它让 P ⊆ NP 成为可直接证明的回归测试。
    - 时间上限取 n^k + k：常数项保证 k = 0 时上限不为零。

  本文件只做定义与「确定性机器是非确定机的特例」这一转换，
  主定理 P ⊆ NP 见文件末尾（若未完成会明确标注）。
-/

import Pnp.Tape

namespace Pnp

/-- 从列表中取第 i 个元素（从 0 开始）；越界返回 none。 -/
def pick {α : Type} : List α → Nat → Option α
  | [], _ => none
  | a :: _, 0 => some a
  | _ :: l, n + 1 => pick l n

/-! ## 确定性机器：判定器与 P -/

namespace DTM

variable {q : Nat}

/-- 在 T 步内到达接受状态。 -/
def AcceptsWithin (M : DTM q) (w : List Bool) (T : Nat) : Prop :=
  (M.run T (M.init w)).state = M.accept

/-- 在 T 步内到达拒绝状态。 -/
def RejectsWithin (M : DTM q) (w : List Bool) (T : Nat) : Prop :=
  (M.run T (M.init w)).state = M.reject

/-- 在 T 步内停机（接受或拒绝）。 -/
def HaltsWithin (M : DTM q) (w : List Bool) (T : Nat) : Prop :=
  M.AcceptsWithin w T ∨ M.RejectsWithin w T

/-- M 是指定时间上限下的判定器：对每个输入都停机，且接受当且仅当属于 L。 -/
def DecidesIn (M : DTM q) (T : Nat → Nat) (L : List Bool → Prop) : Prop :=
  ∀ w : List Bool,
    M.HaltsWithin w (T w.length) ∧
      (M.AcceptsWithin w (T w.length) ↔ L w)

end DTM

/-- P：存在多项式时间上限的确定性判定器。
    要求两个终止状态不同——这是判定器的标准约定；任何判定器都能加一个哑状态满足它，
    因此不改变 P 类本身。 -/
def InP (L : List Bool → Prop) : Prop :=
  ∃ (k q : Nat) (M : DTM q), M.accept ≠ M.reject ∧
    M.DecidesIn (fun n => n ^ k + k) L

/-- EXP：存在指数时间上限的确定性判定器。 -/
def InExp (L : List Bool → Prop) : Prop :=
  ∃ (k q : Nat) (M : DTM q), M.accept ≠ M.reject ∧
    M.DecidesIn (fun n => 2 ^ (n ^ k + k)) L

/-- 2EXP：指数塔 `2^(2^(n^k+k))` 时间上限的确定性判定器。 -/
def In2Exp (L : List Bool → Prop) : Prop :=
  ∃ (k q : Nat) (M : DTM q), M.accept ≠ M.reject ∧
    M.DecidesIn (fun n => 2 ^ (2 ^ (n ^ k + k))) L

/-! ## 非确定性机器：NP -/

/-- 单带非确定性图灵机：每一步可选的转移是有限个，运行时可任选其一。 -/
structure NTM (q : Nat) where
  /-- 转移函数：当前状态与符号给出若干候选动作。 -/
  step   : Fin q → Sym → List (Fin q × Sym × Dir)
  start  : Fin q
  accept : Fin q
  reject : Fin q

namespace NTM

variable {q : Nat}

/-- 格局是否已终止（与确定性版本同义）。 -/
def halted (M : NTM q) (c : Config q) : Bool :=
  c.state == M.accept || c.state == M.reject

/-- 按第 i 个候选动作走一步；没有该候选时返回 none。 -/
def stepWith (M : NTM q) (c : Config q) (i : Nat) : Option (Config q) :=
  match pick (M.step c.state c.tape.read) i with
  | none => none
  | some (q', s, d) => some { state := q', tape := (c.tape.write s).move d }

/-- 按给定的选择序列运行至多 n 步；选择用尽或无效时返回 none。 -/
def runWith (M : NTM q) : Nat → List Nat → Config q → Option (Config q)
  | 0, _, c => some c
  | n + 1, choices, c =>
      -- 用 match 而不是 if：避免依赖式 if 把假设卷进匹配式，便于后续展开
      match M.halted c with
      | true => some c
      | false =>
          match choices with
          | [] => none
          | i :: rest => (M.stepWith c i).bind (fun c'' => M.runWith n rest c'')

/-- `runWith` 在步数非零时的展开式（rfl 引理，便于在证明中定向改写）。 -/
theorem runWith_succ (M : NTM q) (n : Nat) (choices : List Nat) (c : Config q) :
    M.runWith (Nat.succ n) choices c =
      (match M.halted c with
       | true => some c
       | false =>
           match choices with
           | [] => none
           | i :: rest => (M.stepWith c i).bind (fun c'' => M.runWith n rest c'')) := by
  -- 定义上就是这条等式
  cases choices <;> rfl

/-- 停机判断只取决于状态是否为接受或拒绝。 -/
theorem halted_of_state (M : NTM q) (c : Config q)
    (h : c.state = M.accept ∨ c.state = M.reject) : M.halted c = true := by
  rcases h with h | h <;> simp [halted, h]

/-- 已停机的格局：任意步数、任意选择序列都停在原地。 -/
theorem runWith_halted (M : NTM q) (c : Config q) (h : M.halted c = true) :
    ∀ (n : Nat) (choices : List Nat), M.runWith n choices c = some c
  | 0, _ => rfl
  | n + 1, _ => by
      -- 展开一步后命中「已停机」分支
      rw [runWith_succ]
      simp [h]

/-- 如果一条运行在 T 步内停机，那么延长到任意 T' ≥ T 步、
    并在选择序列尾部追加任意元素，结果不变（停机后不再读取选择）。 -/
theorem runWith_extend (M : NTM q) :
    ∀ (T : Nat) (choices : List Nat) (c c' : Config q),
      M.runWith T choices c = some c' → M.halted c' = true →
        ∀ (T' : Nat) (extra : List Nat), T ≤ T' →
          M.runWith T' (choices ++ extra) c = some c' := by
  intro T
  induction T with
  | zero =>
      intro choices c c' h hhalt T' extra _
      -- 0 步运行不消耗选择，c' 就是 c
      simp only [NTM.runWith, Option.some.injEq] at h
      subst h
      exact runWith_halted M c hhalt T' (choices ++ extra)
  | succ T ih =>
      intro choices c c' h hhalt T' extra hle
      rw [runWith_succ] at h
      cases hc : M.halted c with
      | true =>
          -- 起点已停机，直接返回
          simp only [hc, Option.some.injEq] at h
          subst h
          exact runWith_halted M c hc T' (choices ++ extra)
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
                  -- 目标步数 T' 必须非零
                  cases T' with
                  | zero => omega
                  | succ T'' =>
                      rw [runWith_succ]
                      simp only [hc, List.cons_append, hs, Option.bind_some]
                      -- 归纳假设处理剩余步数与剩余选择
                      have hle' : T ≤ T'' := by omega
                      exact ih rest c'' c' h hhalt T'' extra hle'

/-- 初始格局。 -/
def init (M : NTM q) (w : List Bool) : Config q :=
  { state := M.start, tape := Tape.ofInput w }

/-- 存在一条长度不超过 T 的选择序列，走到接受状态。 -/
def AcceptsWithin (M : NTM q) (w : List Bool) (T : Nat) : Prop :=
  ∃ choices : List Nat, choices.length ≤ T ∧
    ∃ c : Config q, M.runWith T choices (M.init w) = some c ∧ c.state = M.accept

/-- **起始态即接受态 ⇒ 任何输入在任何步数内都接受**（退化分支，E 的装配要单列）。
    If the start state is accepting, every input is accepted within any number of steps. -/
theorem acceptsWithin_of_start_accept (M : NTM q) (w : List Bool) (T : Nat)
    (h : M.start = M.accept) : M.AcceptsWithin w T := by
  refine ⟨[], by simp, M.init w, ?_, ?_⟩
  · cases T with
    | zero => rfl
    | succ n =>
        rw [runWith_succ]
        have hh : M.halted (M.init w) = true := by
          simp [halted, init, h]
        rw [hh]
  · exact h

/-- 存在一条长度不超过 T 的选择序列，走到拒绝状态。 -/
def RejectsWithin (M : NTM q) (w : List Bool) (T : Nat) : Prop :=
  ∃ choices : List Nat, choices.length ≤ T ∧
    ∃ c : Config q, M.runWith T choices (M.init w) = some c ∧ c.state = M.reject

/-- 在 T 步内停机：某条分支接受或拒绝。 -/
def HaltsWithin (M : NTM q) (w : List Bool) (T : Nat) : Prop :=
  M.AcceptsWithin w T ∨ M.RejectsWithin w T

/-- N 是指定时间上限下的判定器。 -/
def DecidesIn (M : NTM q) (T : Nat → Nat) (L : List Bool → Prop) : Prop :=
  ∀ w : List Bool,
    M.HaltsWithin w (T w.length) ∧
      (M.AcceptsWithin w (T w.length) ↔ L w)

/-- 接受语义对时间上限单调：T 步内接受 ⇒ 任意 T' ≥ T 也接受。 -/
theorem acceptsWithin_mono (M : NTM q) {w : List Bool} {T T' : Nat} (hle : T ≤ T')
    (h : M.AcceptsWithin w T) : M.AcceptsWithin w T' := by
  rcases h with ⟨choices, hlen, c, hrun, hacc⟩
  have hhalt : M.halted c = true := by
    simp [NTM.halted, hacc]
  refine ⟨choices ++ List.replicate (T' - choices.length) 0, ?_, c, ?_, hacc⟩
  · rw [List.length_append, List.length_replicate]
    have hcT' : choices.length ≤ T' := Nat.le_trans hlen hle
    omega
  · exact NTM.runWith_extend M T choices (M.init w) c hrun hhalt T'
      (List.replicate (T' - choices.length) 0) hle

/-- 拒绝语义对时间上限单调。 -/
theorem rejectsWithin_mono (M : NTM q) {w : List Bool} {T T' : Nat} (hle : T ≤ T')
    (h : M.RejectsWithin w T) : M.RejectsWithin w T' := by
  rcases h with ⟨choices, hlen, c, hrun, hacc⟩
  have hhalt : M.halted c = true := by
    simp [NTM.halted, hacc]
  refine ⟨choices ++ List.replicate (T' - choices.length) 0, ?_, c, ?_, hacc⟩
  · rw [List.length_append, List.length_replicate]
    have hcT' : choices.length ≤ T' := Nat.le_trans hlen hle
    omega
  · exact NTM.runWith_extend M T choices (M.init w) c hrun hhalt T'
      (List.replicate (T' - choices.length) 0) hle

/-- 停机语义对时间上限单调。 -/
theorem haltsWithin_mono (M : NTM q) {w : List Bool} {T T' : Nat} (hle : T ≤ T')
    (h : M.HaltsWithin w T) : M.HaltsWithin w T' :=
  h.elim (fun ha => Or.inl (M.acceptsWithin_mono hle ha))
    (fun hr => Or.inr (M.rejectsWithin_mono hle hr))

/-- 把确定性机器看成「每步只有一个候选」的非确定机。 -/
def ofDTM (M : DTM q) : NTM q where
  step := fun s a => [M.step s a]
  start := M.start
  accept := M.accept
  reject := M.reject

/-! ## 停机规范形：接受 / 拒绝状态不再有候选动作 -/

/-- 停机规范形：把接受、拒绝状态的候选动作清空，其余转移表与原机一致。
    这样「查表失败（相位 14）」就恰好等价于「跑到停机态」或「选择编号越界」。
    Halt normal form: clear the candidate actions at the accept/reject states. -/
def haltNorm (M : NTM q) : NTM q where
  step := fun s a => if s = M.accept ∨ s = M.reject then [] else M.step s a
  start := M.start
  accept := M.accept
  reject := M.reject

/-- 规范形的停机判断与原机完全相同（字段不变）。 -/
theorem haltNorm_halted (M : NTM q) (c : Config q) :
    (M.haltNorm).halted c = M.halted c := rfl

/-- 未停机时状态既不是接受也不是拒绝。 -/
theorem ne_accept_reject_of_not_halted (M : NTM q) (c : Config q)
    (h : M.halted c = false) : c.state ≠ M.accept ∧ c.state ≠ M.reject := by
  constructor
  · intro he
    rw [NTM.halted, he] at h
    simp at h
  · intro he
    rw [NTM.halted, he] at h
    simp at h

/-- 未停机时规范形与原机的转移表逐项一致。 -/
theorem haltNorm_step_of_not_halted (M : NTM q) (c : Config q)
    (h : M.halted c = false) (s : Sym) :
    (M.haltNorm).step c.state s = M.step c.state s := by
  obtain ⟨h1, h2⟩ := ne_accept_reject_of_not_halted M c h
  unfold haltNorm
  dsimp only
  rw [if_neg (by
    intro hh
    rcases hh with he | he
    · exact h1 he
    · exact h2 he)]

/-- 未停机时规范形与原机的「第 i 个候选动作」完全一致。 -/
theorem haltNorm_stepWith_of_not_halted (M : NTM q) (c : Config q) (i : Nat)
    (h : M.halted c = false) :
    (M.haltNorm).stepWith c i = M.stepWith c i := by
  simp only [NTM.stepWith, haltNorm_step_of_not_halted M c h]

/-- 规范形在停机态没有候选动作（任何选择编号都失败）。 -/
theorem haltNorm_stepWith_accept (M : NTM q) (c : Config q) (i : Nat)
    (h : c.state = M.accept) :
    (M.haltNorm).stepWith c i = none := by
  unfold NTM.stepWith
  unfold haltNorm
  dsimp only
  rw [if_pos (Or.inl h)]
  rfl

/-- 规范形在拒绝态没有候选动作。 -/
theorem haltNorm_stepWith_reject (M : NTM q) (c : Config q) (i : Nat)
    (h : c.state = M.reject) :
    (M.haltNorm).stepWith c i = none := by
  unfold NTM.stepWith
  unfold haltNorm
  dsimp only
  rw [if_pos (Or.inr h)]
  rfl

/-- 规范形与原机的 `runWith` 逐点相等（停机判断先于查表，故清空停机态转移无影响）。 -/
theorem haltNorm_runWith (M : NTM q) (n : Nat) (choices : List Nat) (c : Config q) :
    (M.haltNorm).runWith n choices c = M.runWith n choices c := by
  induction n generalizing choices c with
  | zero => rfl
  | succ n ih =>
      rw [NTM.runWith_succ, NTM.runWith_succ, haltNorm_halted]
      cases hc : M.halted c with
      | true => simp only [hc]
      | false =>
          simp only [hc]
          cases choices with
          | nil => simp
          | cons i rest =>
              dsimp only
              rw [haltNorm_stepWith_of_not_halted M c i hc]
              cases hs : M.stepWith c i with
              | none => simp [hs]
              | some c' => simp [hs, ih rest c']

/-- 规范形从自身初始格局出发的运行，与原机运行相等（初始格局差在 `init` 的包装）。 -/
theorem haltNorm_runWith_init (M : NTM q) (n : Nat) (choices : List Nat) (w : List Bool) :
    (M.haltNorm).runWith n choices ((M.haltNorm).init w)
      = M.runWith n choices (M.init w) := by
  simp only [NTM.init, haltNorm]
  exact haltNorm_runWith M n choices _

/-- 接受语义在规范形下不变。 -/
theorem haltNorm_acceptsWithin (M : NTM q) (w : List Bool) (T : Nat) :
    (M.haltNorm).AcceptsWithin w T ↔ M.AcceptsWithin w T := by
  constructor
  · rintro ⟨choices, hlen, c, hrun, hacc⟩
    rw [haltNorm_runWith_init M T choices w] at hrun
    exact ⟨choices, hlen, c, hrun, hacc⟩
  · rintro ⟨choices, hlen, c, hrun, hacc⟩
    refine ⟨choices, hlen, c, ?_, hacc⟩
    rw [haltNorm_runWith_init M T choices w]
    exact hrun

/-- 拒绝语义在规范形下不变。 -/
theorem haltNorm_rejectsWithin (M : NTM q) (w : List Bool) (T : Nat) :
    (M.haltNorm).RejectsWithin w T ↔ M.RejectsWithin w T := by
  constructor
  · rintro ⟨choices, hlen, c, hrun, hacc⟩
    rw [haltNorm_runWith_init M T choices w] at hrun
    exact ⟨choices, hlen, c, hrun, hacc⟩
  · rintro ⟨choices, hlen, c, hrun, hacc⟩
    refine ⟨choices, hlen, c, ?_, hacc⟩
    rw [haltNorm_runWith_init M T choices w]
    exact hrun

/-- 停机语义在规范形下不变。 -/
theorem haltNorm_haltsWithin (M : NTM q) (w : List Bool) (T : Nat) :
    (M.haltNorm).HaltsWithin w T ↔ M.HaltsWithin w T := by
  constructor
  · rintro (ha | hr)
    · exact Or.inl ((haltNorm_acceptsWithin M w T).mp ha)
    · exact Or.inr ((haltNorm_rejectsWithin M w T).mp hr)
  · rintro (ha | hr)
    · exact Or.inl ((haltNorm_acceptsWithin M w T).mpr ha)
    · exact Or.inr ((haltNorm_rejectsWithin M w T).mpr hr)

end NTM

/-- NP：存在多项式时间上限的非确定性判定器（同样要求两个终止状态不同）。 -/
def InNP (L : List Bool → Prop) : Prop :=
  ∃ (k q : Nat) (M : NTM q), M.accept ≠ M.reject ∧
    M.DecidesIn (fun n => n ^ k + k) L

/-! ## 回归测试：确定性机器是非确定机的特例 -/

namespace DTM

variable {q : Nat}

/-- 用全 0 选择序列运行时，非确定机与原来的确定机逐步一致。 -/
theorem ofDTM_runWith_replicate (M : DTM q) :
    ∀ (T : Nat) (c : Config q),
      (NTM.ofDTM M).runWith T (List.replicate T 0) c = some (M.run T c)
  | 0, c => by
      -- 0 步：两边都停在原地
      simp [NTM.runWith, DTM.run]
  | T + 1, c => by
      -- 逐步展开，并利用归纳假设
      simp only [List.replicate_succ]
      rw [NTM.runWith_succ]
      -- 两种定义的停机判断是同一个表达式，先统一
      have hhEq : (NTM.ofDTM M).halted c = M.halted c := rfl
      rw [hhEq]
      cases hh : M.halted c with
      | true =>
          -- 已停机：两边都不再动
          simp [DTM.run, hh]
      | false =>
          -- 未停机：先走第 0 个候选动作，再递归
          simp [DTM.run, hh, NTM.stepWith, NTM.ofDTM, pick, DTM.stepConfig]
          exact ofDTM_runWith_replicate M T (M.stepConfig c)

/-- 任意选择序列若能让确定性机器（视为非确定机）停在某个格局，
    则该格局就是它唯一的确定运行结果。 -/
theorem ofDTM_runWith_eq (M : DTM q) :
    ∀ (T : Nat) (choices : List Nat) (c c' : Config q),
      (NTM.ofDTM M).runWith T choices c = some c' → c' = M.run T c := by
  intro T
  induction T with
  | zero =>
      intro choices c c' h
      simp only [NTM.runWith, Option.some.injEq] at h
      subst h
      rfl
  | succ T ih =>
      intro choices c c' h
      rw [NTM.runWith_succ] at h
      have hhEq : (NTM.ofDTM M).halted c = M.halted c := rfl
      rw [hhEq] at h
      cases hh : M.halted c with
      | true =>
          -- 已停机：立即返回当前格局
          simp only [hh, Option.some.injEq] at h
          subst h
          simp [DTM.run, hh]
      | false =>
          -- 未停机：必须消耗一个选择，且确定性机器只有第 0 个候选有效
          simp only [hh] at h
          cases choices with
          | nil => cases h
          | cons i rest =>
              cases i with
              | zero =>
                  simp only [NTM.stepWith, NTM.ofDTM, pick, Option.bind_some] at h
                  -- 未停机时，确定性机器的一步就是 stepConfig
                  have hr : M.run (T + 1) c = M.run T (M.stepConfig c) := by
                    simp [DTM.run, hh]
                  rw [hr]
                  exact ih rest (M.stepConfig c) c' h
              | succ i =>
                  -- 候选编号非 0：单候选列表取不到，运行结果为 none，矛盾
                  cases h

/-- 接受语义在确定性/非确定性两种定义下一致。 -/
theorem ofDTM_acceptsWithin (M : DTM q) (w : List Bool) (T : Nat) :
    (NTM.ofDTM M).AcceptsWithin w T ↔ M.AcceptsWithin w T := by
  constructor
  · -- 非确定地接受 ⇒ 确定性运行也接受（由运行结果唯一性）
    rintro ⟨choices, _, c, hrun, hacc⟩
    have hc : c = M.run T (M.init w) := ofDTM_runWith_eq M T choices (M.init w) c hrun
    rw [hc] at hacc
    exact hacc
  · -- 确定地接受 ⇒ 取全 0 选择序列即可
    intro h
    refine ⟨List.replicate T 0, by simp, M.run T (M.init w), ?_, h⟩
    exact ofDTM_runWith_replicate M T (M.init w)

/-- 停机语义同样一致。 -/
theorem ofDTM_haltsWithin (M : DTM q) (w : List Bool) (T : Nat) :
    (NTM.ofDTM M).HaltsWithin w T ↔ M.HaltsWithin w T := by
  constructor
  · rintro (h | h)
    · exact Or.inl ((ofDTM_acceptsWithin M w T).mp h)
    · -- 拒绝语义与接受对称，此处直接展开定义
      rcases h with ⟨choices, _, c, hrun, hrej⟩
      have hc : c = M.run T (M.init w) := ofDTM_runWith_eq M T choices (M.init w) c hrun
      rw [hc] at hrej
      exact Or.inr hrej
  · rintro (h | h)
    · exact Or.inl ((ofDTM_acceptsWithin M w T).mpr h)
    · refine Or.inr ⟨List.replicate T 0, by simp, M.run T (M.init w), ?_, h⟩
      exact ofDTM_runWith_replicate M T (M.init w)

end DTM

/-- 回归测试 R1：P ⊆ NP。 -/
theorem inP_subset_inNP {L : List Bool → Prop} (h : InP L) : InNP L := by
  rcases h with ⟨k, q, M, hne, hM⟩
  refine ⟨k, q, NTM.ofDTM M, hne, ?_⟩
  intro w
  exact ⟨(DTM.ofDTM_haltsWithin M w _).mpr (hM w).1,
    (DTM.ofDTM_acceptsWithin M w _).trans (hM w).2⟩

/-! ## 运行语义的基本引理 -/

namespace DTM

variable {q : Nat}

/-- 已停机的格局，再跑任意步数都停在原地。 -/
theorem run_of_halted (M : DTM q) (c : Config q) (h : M.halted c = true) :
    ∀ n : Nat, M.run n c = c
  | 0 => rfl
  | n + 1 => by
      -- 停机判断为真时，run 直接返回原格局
      simp [run, h]

/-- `stepConfig` 的状态分量就是 `step` 结果的第一个分量。 -/
theorem stepConfig_state (M : DTM q) (c : Config q) :
    (M.stepConfig c).state = (M.step c.state c.tape.read).1 := rfl

/-- 运行可以分段拼接：先跑 a 步、再跑 b 步，等于一共跑 a+b 步。 -/
theorem run_add (M : DTM q) (a b : Nat) (c : Config q) :
    M.run (a + b) c = M.run b (M.run a c) := by
  induction a generalizing b c with
  | zero => simp [run]
  | succ a ih =>
      -- (a+1)+b = (a+b)+1，展开外层一步后分「是否已停机」讨论
      rw [Nat.succ_add]
      simp only [run]
      by_cases hh : M.halted c
      · -- 已停机：两边都不动
        simp [hh, run_of_halted M c hh]
      · -- 未停机：把一步交给归纳假设
        simp only [hh]
        exact ih b (M.stepConfig c)

/-- 未停机时，`run (n+1)` 等于「先走一步，再继续 n 步」。 -/
theorem run_succ_of_not_halted (M : DTM q) (n : Nat) (c : Config q)
    (h : M.halted c = false) :
    M.run (n + 1) c = M.run n (M.stepConfig c) := by
  rw [DTM.run]
  simp only [h, Bool.false_eq_true, ite_false]

/-- 从尾部推进一步：`n` 步后的格局未停机时，再走一步就是它的 `stepConfig`。 -/
theorem run_succ_last (M : DTM q) (n : Nat) (c : Config q)
    (h : M.halted (M.run n c) = false) :
    M.run (n + 1) c = M.stepConfig (M.run n c) := by
  rw [DTM.run_add M n 1 c, DTM.run]
  simp only [h, Bool.false_eq_true, ite_false]
  rfl

/-- **终点非终止 ⇒ 全程未停机**：若 `n` 步后的状态既非接受也非拒绝，
    则前 `n` 步（不含第 `n` 步之后的格局）内从未停机。
    If the state after `n` steps is neither accept nor reject, the machine never halted
    during those `n` steps. Used to feed `run_embed`-style composition lemmas with a
    single endpoint fact instead of a step-by-step invariant. -/
theorem halted_false_before (M : DTM q) (n : Nat) (c : Config q)
    (hacc : (M.run n c).state ≠ M.accept) (hrej : (M.run n c).state ≠ M.reject) :
    ∀ k, k < n → M.halted (M.run k c) = false := by
  intro k hk
  cases hh : M.halted (M.run k c) with
  | false => rfl
  | true =>
      -- 若在第 k 步已停机，则此后格局不再变化，终点状态也会终止，矛盾
      exfalso
      have hfix : M.run n c = M.run k c := by
        rw [show n = k + (n - k) from by omega, DTM.run_add M k (n - k) c]
        exact run_of_halted M (M.run k c) hh (n - k)
      rw [← hfix] at hh
      have hfalse : M.halted (M.run n c) = false := by
        rw [DTM.halted, Bool.or_eq_false_iff]
        exact ⟨beq_eq_false_iff_ne.mpr hacc, beq_eq_false_iff_ne.mpr hrej⟩
      rw [hfalse] at hh
      exact Bool.noConfusion hh

/-- 停机判断只取决于当前状态是否等于接受或拒绝状态。 -/
theorem halted_of_accept_or_reject (M : DTM q) (c : Config q)
    (h : c.state = M.accept ∨ c.state = M.reject) : M.halted c = true := by
  rcases h with h | h <;> simp [halted, h]

/-- **接受态冻结**：若跑 `n` 步后已停在接受态，再多跑 `m` 步格局不变。
    Acceptance freezes: once the run of `n` steps ends in the accept state, running `m` more
    steps changes nothing. -/
theorem run_add_of_accept {q : Nat} (M : DTM q) (c : Config q) (n m : Nat)
    (h : (M.run n c).state = M.accept) : M.run (n + m) c = M.run n c := by
  rw [run_add]
  exact run_of_halted M (M.run n c)
    (halted_of_accept_or_reject M (M.run n c) (Or.inl h)) m

/-- **接受态冻结（状态形式）**：跑 `n` 步后状态为接受态，则再跑 `m` 步状态仍是接受态。
    Acceptance freezes (state form): if the run of `n` steps ends accepting, so does the run
    of `n + m` steps. -/
theorem run_add_state_of_accept {q : Nat} (M : DTM q) (c : Config q) (n m : Nat)
    (h : (M.run n c).state = M.accept) : (M.run (n + m) c).state = M.accept := by
  rw [run_add]
  have hh : M.halted (M.run n c) = true :=
    halted_of_accept_or_reject M (M.run n c) (Or.inl h)
  rw [run_of_halted M (M.run n c) hh m]
  exact h

/-- 时间上限放宽后仍是判定器：T ≤ T' 逐点成立，则 DecidesIn T ⇒ DecidesIn T'。 -/
theorem decidesIn_mono (M : DTM q) {T T' : Nat → Nat}
    (hle : ∀ n : Nat, T n ≤ T' n) {L : List Bool → Prop}
    (h : M.DecidesIn T L) : M.DecidesIn T' L := by
  intro w
  obtain ⟨hhalt, hacc⟩ := h w
  -- 在 T 步内已停机，故 T' 步的格局与 T 步相同
  have hrun : M.run (T' w.length) (M.init w) = M.run (T w.length) (M.init w) := by
    have hsum : T w.length + (T' w.length - T w.length) = T' w.length :=
      Nat.add_sub_of_le (hle w.length)
    rw [← hsum, run_add]
    apply run_of_halted
    rcases hhalt with hA | hR
    · exact halted_of_accept_or_reject M _ (Or.inl hA)
    · exact halted_of_accept_or_reject M _ (Or.inr hR)
  constructor
  · rcases hhalt with hA | hR
    · exact Or.inl (by simpa [AcceptsWithin, hrun] using hA)
    · exact Or.inr (by simpa [RejectsWithin, hrun] using hR)
  · simpa [AcceptsWithin, hrun] using hacc

end DTM

/-- `n ≤ 2 ^ n`，用于把多项式时间上限塞进指数上限。 -/
theorem le_two_pow : ∀ n : Nat, n ≤ 2 ^ n
  | 0 => by simp
  | n + 1 => by
      have ih : n ≤ 2 ^ n := le_two_pow n
      have hpos : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have hdouble : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by
        -- 核心库里的名字是 Nat.pow_succ
        rw [Nat.pow_succ]
        omega
      omega

/-- P ⊆ EXP：多项式时间判定器自动满足指数时间上限。 -/
theorem inP_subset_inExp {L : List Bool → Prop} (h : InP L) : InExp L := by
  rcases h with ⟨k, q, M, hne, hM⟩
  refine ⟨k, q, M, hne, ?_⟩
  intro w
  obtain ⟨hhalt, hacc⟩ := hM w
  -- T 为多项式上限，2^T 为指数上限
  have hle : w.length ^ k + k ≤ 2 ^ (w.length ^ k + k) := le_two_pow _
  have hhalted : M.halted (M.run (w.length ^ k + k) (M.init w)) = true :=
    DTM.halted_of_accept_or_reject M _ hhalt
  -- 一旦在 T 步内停机，跑更多步也停在同一个格局
  have hrun :
      M.run (2 ^ (w.length ^ k + k)) (M.init w)
        = M.run (w.length ^ k + k) (M.init w) := by
    -- 把指数上限拆成「T 步 + 剩余步」，先跑到 T 步，剩余步数原地不动
    have hT : w.length ^ k + k + (2 ^ (w.length ^ k + k) - (w.length ^ k + k))
        = 2 ^ (w.length ^ k + k) := Nat.add_sub_of_le hle
    rw [← hT, DTM.run_add]
    exact DTM.run_of_halted M _ hhalted _
  constructor
  · -- 停机性
    rcases hhalt with hA | hR
    · exact Or.inl (by simpa [DTM.AcceptsWithin, hrun] using hA)
    · exact Or.inr (by simpa [DTM.RejectsWithin, hrun] using hR)
  · -- 接受语义
    simpa [DTM.AcceptsWithin, hrun] using hacc

/-! ## 闭合性质：P 对补集封闭 -/

namespace DTM

/-- 交换接受与拒绝状态的机器：它接受的输入恰是原机器拒绝的输入。 -/
def swap (M : DTM q) : DTM q :=
  { M with accept := M.reject, reject := M.accept }

/-- 交换终止状态不改变「是否停机」。 -/
theorem swap_halted (M : DTM q) (c : Config q) :
    (M.swap).halted c = M.halted c := by
  simp [halted, swap, Bool.or_comm]

/-- 交换终止状态不改变单步语义。 -/
theorem swap_stepConfig (M : DTM q) (c : Config q) :
    (M.swap).stepConfig c = M.stepConfig c := rfl

/-- 交换终止状态不改变运行轨迹。 -/
theorem swap_run (M : DTM q) (T : Nat) (c : Config q) :
    (M.swap).run T c = M.run T c := by
  induction T generalizing c with
  | zero => rfl
  | succ T ih =>
      simp only [run, swap_halted, swap_stepConfig]
      by_cases hh : M.halted c
      · simp [hh]
      · simp only [hh]
        exact ih (M.stepConfig c)

/-- 交换后的「接受」等于原机器的「拒绝」。 -/
theorem swap_accepts (M : DTM q) (w : List Bool) (T : Nat) :
    (M.swap).AcceptsWithin w T ↔ M.RejectsWithin w T := by
  unfold AcceptsWithin RejectsWithin
  rw [swap_run]
  simp [init, swap]

/-- 交换后的「拒绝」等于原机器的「接受」。 -/
theorem swap_rejects (M : DTM q) (w : List Bool) (T : Nat) :
    (M.swap).RejectsWithin w T ↔ M.AcceptsWithin w T := by
  unfold RejectsWithin AcceptsWithin
  rw [swap_run]
  simp [init, swap]

end DTM

/-- P 对补集封闭：若 L ∈ P，则 {w | w ∉ L} ∈ P。 -/
theorem inP_compl {L : List Bool → Prop} (h : InP L) :
    InP (fun w => ¬ L w) := by
  rcases h with ⟨k, q, M, hne, hM⟩
  refine ⟨k, q, M.swap, ?_, ?_⟩
  · -- 交换后两个终止状态仍然不同
    exact fun hh => hne hh.symm
  · intro w
    obtain ⟨hhalt, hacc⟩ := hM w
    constructor
    · -- 停机性：接受/拒绝互换，析取不变
      rcases hhalt with hA | hR
      · exact Or.inr ((DTM.swap_rejects M w _).mpr hA)
      · exact Or.inl ((DTM.swap_accepts M w _).mpr hR)
    · constructor
      · -- 交换后接受 ⇒ 原机器拒绝 ⇒ 不在 L 中
        intro hsw hL
        have hR : M.RejectsWithin w _ := (DTM.swap_accepts M w _).mp hsw
        have hA : M.AcceptsWithin w _ := hacc.mpr hL
        -- 接受与拒绝同时成立会迫使两个终止状态相等
        have hA' : (M.run (w.length ^ k + k) (M.init w)).state = M.accept := hA
        have hR' : (M.run (w.length ^ k + k) (M.init w)).state = M.reject := hR
        exact hne (hA'.symm.trans hR')
      · -- 不在 L 中 ⇒ 原机器不可能是接受 ⇒ 停机后必为拒绝
        intro hLnot
        have hnotA : ¬ M.AcceptsWithin w _ := fun hA => hLnot (hacc.mp hA)
        rcases hhalt with hA | hR
        · exact absurd hA hnotA
        · exact (DTM.swap_accepts M w _).mpr hR

/-- EXP 对补集封闭：若 L ∈ EXP，则 {w | w ∉ L} ∈ EXP。 -/
theorem inExp_compl {L : List Bool → Prop} (h : InExp L) :
    InExp (fun w => ¬ L w) := by
  rcases h with ⟨k, q, M, hne, hM⟩
  refine ⟨k, q, M.swap, ?_, ?_⟩
  · -- 交换后两个终止状态仍然不同
    exact fun hh => hne hh.symm
  · intro w
    obtain ⟨hhalt, hacc⟩ := hM w
    constructor
    · -- 停机性：接受/拒绝互换，析取不变
      rcases hhalt with hA | hR
      · exact Or.inr ((DTM.swap_rejects M w _).mpr hA)
      · exact Or.inl ((DTM.swap_accepts M w _).mpr hR)
    · constructor
      · -- 交换后接受 ⇒ 原机器拒绝 ⇒ 不在 L 中
        intro hsw hL
        have hR : M.RejectsWithin w _ := (DTM.swap_accepts M w _).mp hsw
        have hA : M.AcceptsWithin w _ := hacc.mpr hL
        have hA' : (M.run (2 ^ (w.length ^ k + k)) (M.init w)).state = M.accept := hA
        have hR' : (M.run (2 ^ (w.length ^ k + k)) (M.init w)).state = M.reject := hR
        exact hne (hA'.symm.trans hR')
      · -- 不在 L 中 ⇒ 原机器不可能是接受 ⇒ 停机后必为拒绝
        intro hLnot
        have hnotA : ¬ M.AcceptsWithin w _ := fun hA => hLnot (hacc.mp hA)
        rcases hhalt with hA | hR
        · exact absurd hA hnotA
        · exact (DTM.swap_accepts M w _).mpr hR

/-! ## coNP -/

/-- coNP：补集属于 NP 的语言类。 -/
def IncoNP (L : List Bool → Prop) : Prop := InNP (fun w => ¬ L w)

/-- P ⊆ coNP：先对补集用 P ⊆ NP，再用 P 对补集封闭。 -/
theorem inP_subset_incoNP {L : List Bool → Prop} (h : InP L) : IncoNP L :=
  inP_subset_inNP (inP_compl h)

/-- EXP ⊆ 2EXP：同一台机器，把指数上限再套一层指数。 -/
theorem inExp_subset_in2Exp {L : List Bool → Prop} (h : InExp L) : In2Exp L := by
  rcases h with ⟨k, q, M, hne, hM⟩
  refine ⟨k, q, M, hne, DTM.decidesIn_mono M ?_ hM⟩
  intro n
  -- 2^T ≤ 2^(2^T)，因为 T ≤ 2^T
  have h1 : n ^ k + k ≤ 2 ^ (n ^ k + k) := le_two_pow _
  exact Nat.pow_le_pow_right (by decide : 0 < 2) h1

/-- P ⊆ 2EXP。 -/
theorem inP_subset_in2Exp {L : List Bool → Prop} (h : InP L) : In2Exp L :=
  inExp_subset_in2Exp (inP_subset_inExp h)

end Pnp
