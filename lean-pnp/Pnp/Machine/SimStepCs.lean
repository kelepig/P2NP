/-
  文件：Pnp/Machine/SimStepCs.lean
  主题：把「区域迭代 `stepNs` 在 ≤ t 步内停在接受态」翻译成「无计数的区域迭代
        `stepCs`（规范形 `haltNorm` 的单步）沿某个前缀直达该接受态」。

  背景（B5 反向方向，承接 auto-run-log #117）：
    - `exists_stepNs_accept_of_bruteForce` 从暴力搜索给出 `stepNs M t cs x = some z`（`z` 接受）；
    - `exists_passRun_of_stepCs_map`（#114）需要 `stepCs (haltNorm.step) (c :: cs) x = some y`；
    - 二者之间缺少一座桥：`stepNs` 带步数计数 `t` 与「提前停机即返回」语义，而 `stepCs`
      只按列表折叠、遇停机态（规范形查表为空）即失败。
    本文件补上这座桥：`stepNs` 的接受结果对应 `stepCs` 沿「实际消耗的前缀」成功，
    且该前缀长度不超过原选择列表长度。停机前各步状态均非接受/拒绝态，故把 `M.step`
    换成规范形 `(M.haltNorm).step` 不影响前缀内的折叠结果。

  Bridge from counted region iteration (`stepNs`) reaching an accepting state to the
  uncounted fold (`stepCs`) over the actually-consumed prefix.
-/

import Pnp.Machine.SimRegion
import Pnp.Machine.SimPass

namespace Pnp

namespace DTM

/-- 区域单步只读当前 `(状态, 符号)` 处的转移表：两表在该处相同则单步结果相同。
    `Reg.step` only consults the table at the current `(state, symbol)`. -/
theorem regStep_congr {q : Nat} {tab1 tab2 : Fin q → Sym → List (Fin q × Sym × Dir)}
    (c : Nat) (x : Reg q) (h : tab1 x.state x.cur = tab2 x.state x.cur) :
    Reg.step tab1 c x = Reg.step tab2 c x := by
  simp only [Reg.step]
  rw [h]

/-- **计数迭代 ⇒ 无计数折叠**：若带步数计数的区域迭代 `stepNs M t cs x` 停在接受态 `z`，
    则存在选择列表的一个前缀 `cs'`（长度 ≤ `cs`），使无计数折叠
    `stepCs (M.haltNorm).step` 沿 `cs'` 恰好到达同一 `z`。

    微妙处：`stepNs` 在遇到停机态时「提前返回」（不再消费剩余选择），而接受态恰是停机态；
    因此只需取「走到接受态的这段前缀」，其内每步的前一状态都非停机，`M.step` 与规范形一致。
    Counted iteration reaching an accepting state implies the uncounted canonical fold
    (`haltNorm` step) over the consumed prefix reaches the same state. -/
theorem exists_stepCs_accept_of_stepNs {q : Nat} (M : NTM q) :
    ∀ (t : Nat) (cs : List Nat) (x z : Reg q),
      stepNs M t cs x = some z → z.state = M.accept →
      ∃ cs', cs'.length ≤ cs.length ∧ (∀ a ∈ cs', a ∈ cs) ∧
        stepCs (M.haltNorm).step cs' x = some z := by
  intro t
  induction t with
  | zero =>
      intro cs x z h _
      -- `stepNs M 0 cs x = some x`：零步即原地，前缀取空
      simp only [stepNs] at h
      have hz : x = z := Option.some.inj h
      subst hz
      exact ⟨[], Nat.zero_le _, by simp, rfl⟩
  | succ t ih =>
      intro cs x z h hacc
      -- 按选择列表是否为空分派，再按当前是否停机分派
      cases cs with
      | nil =>
          simp only [stepNs] at h
          cases hh : M.halted x.toConfig with
          | true =>
              -- 已停机：`stepNs` 原地返回 `x`，前缀取空
              rw [hh] at h
              have hz : x = z := Option.some.inj h
              subst hz
              exact ⟨[], Nat.zero_le _, by simp, rfl⟩
          | false =>
              -- 未停机且无选择：返回 none，与 `= some z` 矛盾
              rw [hh] at h
              exact absurd h (by simp)
      | cons c cs0 =>
          simp only [stepNs] at h
          cases hh : M.halted x.toConfig with
          | true =>
              -- 已停机：原地返回 `x`
              rw [hh] at h
              have hz : x = z := Option.some.inj h
              subst hz
              exact ⟨[], Nat.zero_le _, by simp, rfl⟩
          | false =>
              -- 未停机：先走一步到 `x1`，再用归纳假设处理剩余选择
              rw [hh] at h
              cases hs : Reg.step M.step c x with
              | none =>
                  simp only [hs] at h
                  exact absurd h (by simp)
              | some x1 =>
                  simp only [hs, Option.bind_some] at h
                  obtain ⟨cs', hlen, hmem, hfold⟩ := ih cs0 x1 z h hacc
                  refine ⟨c :: cs', ?_, ?_, ?_⟩
                  · simp only [List.length_cons]
                    omega
                  · -- 前缀成员仍来自原选择列表（c 直接来自头部，其余来自归纳）
                    intro a ha
                    rcases List.mem_cons.mp ha with rfl | ha'
                    · exact List.mem_cons_self
                    · exact List.mem_cons_of_mem c (hmem a ha')
                  · -- 当前步非停机，故规范形与 `M.step` 在该 `(状态, 符号)` 处一致
                    simp only [stepCs]
                    have htab : (M.haltNorm).step x.state x.cur = M.step x.state x.cur :=
                      NTM.haltNorm_step_of_not_halted M x.toConfig hh x.cur
                    have hstep_eq : Reg.step (M.haltNorm).step c x = Reg.step M.step c x :=
                      regStep_congr c x htab
                    rw [hstep_eq, hs, Option.bind_some]
                    exact hfold

/-- **计数迭代的接受前缀仍取自原选择列表**：与 `exists_accept_of_runWith`（SimRegion）同结论，
    额外保证实际消耗的前缀 `cs'` 每个元素都来自原选择列表 `cs`。用于把「选择序列各项都满足
    某界」的条件传递到前缀（后续接 `exists_passRun_of_stepCs_map`）。
    Strengthened completeness: the consumed prefix `cs'` is a sub-list (by membership) of the
    original choices `cs`, so entry-wise bounds transfer to it. -/
theorem exists_stepNs_accept_of_runWith_mem {q : Nat} (M : NTM q) :
    ∀ (n : Nat) (cs : List Nat) (x : Reg q) (y : Config q),
      x.MarkersOK → n ≤ x.pre.length → n ≤ x.post.length →
      M.runWith n cs x.toConfig = some y → y.state = M.accept →
      ∃ (t : Nat) (cs' : List Nat) (z : Reg q),
        t ≤ n ∧ cs'.length ≤ t ∧ (∀ a ∈ cs', a ∈ cs) ∧
          stepNs M t cs' x = some z ∧ z.state = M.accept ∧ z.toConfig = y := by
  intro n
  induction n with
  | zero =>
      intro cs x y hx hd1 hd2 h hacc
      simp only [NTM.runWith, Option.some.injEq] at h
      subst h
      exact ⟨0, [], x, by omega, by simp, by simp, rfl, hacc, rfl⟩
  | succ n ih =>
      intro cs x y hx hd1 hd2 h hacc
      rw [NTM.runWith_succ] at h
      cases hh : M.halted x.toConfig with
      | true =>
          simp only [hh, Option.some.injEq] at h
          subst h
          exact ⟨0, [], x, by omega, by simp, by simp, rfl, hacc, rfl⟩
      | false =>
          simp only [hh] at h
          cases cs with
          | nil => cases h
          | cons c cs =>
              cases hstep : M.stepWith x.toConfig c with
              | none =>
                  simp only [hstep] at h
                  cases h
              | some c1 =>
                  simp only [hstep, Option.bind_some] at h
                  have hpre : x.pre ≠ [] := by
                    intro hnil
                    rw [hnil] at hd1
                    simp at hd1
                  have hpost : x.post ≠ [] := by
                    intro hnil
                    rw [hnil] at hd2
                    simp at hd2
                  obtain ⟨z, hzstep, hzc⟩ :=
                    exists_step_of_stepWith M x c hx hpre hpost c1 hstep
                  have hzok : z.MarkersOK := Reg.step_markers hzstep hx
                  obtain ⟨hz1, hz2⟩ := Reg.step_len hzstep
                  have hrun' : M.runWith n cs z.toConfig = some y := by
                    rw [← hzc]
                    exact h
                  obtain ⟨t, cs', z', htn, hlen, hmem, hit, hacc', hzy⟩ :=
                    ih cs z y hzok (by omega) (by omega) hrun' hacc
                  refine ⟨t + 1, c :: cs', z', by omega, ?_, ?_, ?_, hacc', hzy⟩
                  · simp only [List.length_cons]
                    omega
                  · -- 头部 `c` 直接来自原列表，其余来自归纳的成员事实
                    intro a ha
                    rcases List.mem_cons.mp ha with rfl | ha'
                    · exact List.mem_cons_self
                    · exact List.mem_cons_of_mem c (hmem a ha')
                  · simp only [stepNs, hh, hzstep, Option.bind_some]
                    exact hit

/-- **计数迭代消耗的恰是前缀**：`runWith` 停在接受态时，区域迭代 `stepNs` 消耗的选择正是
    原列表的前缀 `cs.take t`（比 `exists_stepNs_accept_of_runWith_mem` 的成员关系更强）。
    接受方向的「分支块列表前缀 = 接受通路」依赖这一点。
    The counted iteration consumes a genuine prefix `cs.take t` of the choice list. -/
theorem exists_stepNs_take_accept_of_runWith {q : Nat} (M : NTM q) :
    ∀ (n : Nat) (cs : List Nat) (x : Reg q) (y : Config q),
      x.MarkersOK → n ≤ x.pre.length → n ≤ x.post.length →
      M.runWith n cs x.toConfig = some y → y.state = M.accept →
      ∃ (t : Nat) (z : Reg q), t ≤ n ∧ t ≤ cs.length ∧
        stepNs M t (cs.take t) x = some z ∧ z.state = M.accept ∧ z.toConfig = y := by
  intro n
  induction n with
  | zero =>
      intro cs x y hx hd1 hd2 h hacc
      simp only [NTM.runWith, Option.some.injEq] at h
      subst h
      exact ⟨0, x, by omega, by simp, rfl, hacc, rfl⟩
  | succ n ih =>
      intro cs x y hx hd1 hd2 h hacc
      rw [NTM.runWith_succ] at h
      cases hh : M.halted x.toConfig with
      | true =>
          simp only [hh, Option.some.injEq] at h
          subst h
          exact ⟨0, x, by omega, by simp, rfl, hacc, rfl⟩
      | false =>
          simp only [hh] at h
          cases cs with
          | nil => cases h
          | cons c cs =>
              cases hstep : M.stepWith x.toConfig c with
              | none =>
                  simp only [hstep] at h
                  cases h
              | some c1 =>
                  simp only [hstep, Option.bind_some] at h
                  have hpre : x.pre ≠ [] := by
                    intro hnil
                    rw [hnil] at hd1
                    simp at hd1
                  have hpost : x.post ≠ [] := by
                    intro hnil
                    rw [hnil] at hd2
                    simp at hd2
                  obtain ⟨z, hzstep, hzc⟩ :=
                    exists_step_of_stepWith M x c hx hpre hpost c1 hstep
                  have hzok : z.MarkersOK := Reg.step_markers hzstep hx
                  obtain ⟨hz1, hz2⟩ := Reg.step_len hzstep
                  have hrun' : M.runWith n cs z.toConfig = some y := by
                    rw [← hzc]
                    exact h
                  obtain ⟨t, z', htn, hlen, hit, hacc', hzy⟩ :=
                    ih cs z y hzok (by omega) (by omega) hrun' hacc
                  refine ⟨t + 1, z', by omega, by simp; omega, ?_, hacc', hzy⟩
                  simp only [List.take_succ_cons, stepNs, hh, hzstep, Option.bind_some]
                  exact hit

/-- **接受前缀是真正的「取前 `t'` 项」**：`stepNs` 停在接受态时，消耗的选择恰是原列表的
    前缀 `cs.take t'`（`exists_stepCs_accept_of_stepNs` 只保证成员关系，这里给出前缀等式）。
    这是接受方向「分支块列表的前缀就是接受通路」的关键一步。
    The consumed choices form a genuine prefix `cs.take t'` of the original list. -/
theorem exists_stepCs_take_accept_of_stepNs {q : Nat} (M : NTM q) :
    ∀ (t : Nat) (cs : List Nat) (x z : Reg q),
      stepNs M t cs x = some z → z.state = M.accept →
      ∃ t' : Nat, t' ≤ t ∧ t' ≤ cs.length ∧
        stepCs (M.haltNorm).step (cs.take t') x = some z := by
  intro t
  induction t with
  | zero =>
      intro cs x z h _
      simp only [stepNs] at h
      have hz : x = z := Option.some.inj h
      subst hz
      exact ⟨0, Nat.zero_le _, Nat.zero_le _, rfl⟩
  | succ t ih =>
      intro cs x z h hacc
      cases cs with
      | nil =>
          simp only [stepNs] at h
          cases hh : M.halted x.toConfig with
          | true =>
              rw [hh] at h
              have hz : x = z := Option.some.inj h
              subst hz
              exact ⟨0, Nat.zero_le _, Nat.zero_le _, rfl⟩
          | false =>
              rw [hh] at h
              exact absurd h (by simp)
      | cons c cs0 =>
          simp only [stepNs] at h
          cases hh : M.halted x.toConfig with
          | true =>
              rw [hh] at h
              have hz : x = z := Option.some.inj h
              subst hz
              exact ⟨0, Nat.zero_le _, Nat.zero_le _, rfl⟩
          | false =>
              rw [hh] at h
              cases hs : Reg.step M.step c x with
              | none =>
                  simp only [hs] at h
                  exact absurd h (by simp)
              | some x1 =>
                  simp only [hs, Option.bind_some] at h
                  obtain ⟨t', ht'1, ht'2, hfold⟩ := ih cs0 x1 z h hacc
                  refine ⟨t' + 1, by omega, by simp; omega, ?_⟩
                  simp only [List.take_succ_cons, stepCs]
                  have htab : (M.haltNorm).step x.state x.cur = M.step x.state x.cur :=
                    NTM.haltNorm_step_of_not_halted M x.toConfig hh x.cur
                  have hstep_eq : Reg.step (M.haltNorm).step c x = Reg.step M.step c x :=
                    regStep_congr c x htab
                  rw [hstep_eq, hs, Option.bind_some]
                  exact hfold

end DTM

end Pnp
