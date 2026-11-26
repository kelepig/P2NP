/-
  文件：Pnp/Machine/ObsPhase.lean
  File: Pnp/Machine/ObsPhase.lean

  主题：外层枚举器的**运行相位机** `obsPhase`。它逐字照抄观察机 `simObs` 的转移表，
        只把「进入分支失败哨兵 `obsFail`」的转移改接为进入逃生态 `obsEsc`
        （`obsEsc` 是本机的拒绝态，等于停机），从而外层循环可以从失败处继续推进到下一分支；
        `obsAcc` 仍映射为接受态。
  Topic: `obsPhase` — `simObs`'s transition table with the fail-sentinel transition redirected
  to an escape state (this machine's reject state), so the outer enumeration can continue to
  the next branch. `obsAcc` stays the accept state.

  本文件给出（#224）：
    - `obsEsc` / `embOb` / `obsPhase` 与状态编号引理；
    - 单步：`obsPhase_step_emb`（公共展开）、`obsPhase_step_copy`（照抄）、
      `obsPhase_step_escape`（改接逃逸）；
    - 停机判定 `simObs_halted_of_ne` / `obsPhase_halted_inner`；
    - 整段：`obsPhase_run_copy`（前缀无哨兵 ⇒ 照抄 n 步）、
      `obsPhase_run_escape`（第 n 步进入失败 ⇒ 第 n+1 步到逃生态）。
  This file gives the escape state, the embedding, the machine, one-step lemmas, the halting
  criterion and the two whole-run facts (copy / escape).
-/

import Pnp.Machine.SimDecide

namespace Pnp

namespace DTM

/-- 逃生态编号：`simObs` 状态空间（`stateCountO q b`）之后再加一格。
    Escape state index, one past `simObs`'s state space. -/
def obsEsc (q b : Nat) : Fin (stateCountO q b + 1) :=
  ⟨stateCountO q b, by unfold stateCountO; omega⟩

/-- `simObs` 状态嵌入 `obsPhase`：编号不变。
    `simObs` states embedded into `obsPhase` (same index). -/
def embOb (q b : Nat) : Fin (stateCountO q b) → Fin (stateCountO q b + 1) :=
  fun s => ⟨s.val, by have := s.isLt; omega⟩

/-- **运行相位机**：照抄 `simObs`，但凡「下一步 = `obsFail`」改接逃生态 `obsEsc`（拒绝态）。
    The run-phase machine: `simObs`'s table with transitions landing on `obsFail`
    redirected to `obsEsc`, the reject state. -/
def obsPhase (q b : Nat) (M : NTM q) : DTM (stateCountO q b + 1) where
  step := fun st a =>
    if hE : st.val < stateCountO q b then
      let r := (simObs q b M).step ⟨st.val, hE⟩ a
      if hr : r.1 = obsFail q b then (obsEsc q b, a, Dir.stay)
      else (embOb q b r.1, r.2.1, r.2.2)
    else (st, a, Dir.stay)
  start := embOb q b (simObs q b M).start
  accept := embOb q b (obsAcc q b)
  reject := obsEsc q b

/-- 逃生态编号就是 `stateCountO q b`。 The escape index is `stateCountO q b`. -/
theorem obsEsc_val (q b : Nat) : (obsEsc q b).val = stateCountO q b := rfl

/-- 接受态编号与 `obsAcc` 相同。 The accept index equals `obsAcc`'s index. -/
theorem obsPhase_accept_val (q b : Nat) (M : NTM q) :
    (obsPhase q b M).accept.val = stateCountD q b := rfl

/-- 拒绝态编号 = 逃生态。 The reject index is the escape index. -/
theorem obsPhase_reject_val (q b : Nat) (M : NTM q) :
    (obsPhase q b M).reject.val = stateCountO q b := rfl

/-- **前缀无哨兵 ⇒ `simObs` 不停机**。 No sentinel in the state ⇒ `simObs` has not halted. -/
theorem simObs_halted_of_ne (q b : Nat) (M : NTM q) (c : Config (stateCountO q b))
    (h1 : c.state ≠ obsAcc q b) (h2 : c.state ≠ obsFail q b) :
    (simObs q b M).halted c = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  exact ⟨beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2⟩

/-- **嵌入态不停机**（除非原状态是接受哨兵）。 An embedded state never halts unless it is
    the accept sentinel. -/
theorem obsPhase_halted_inner (q b : Nat) (M : NTM q) (s : Fin (stateCountO q b))
    (hne : s ≠ obsAcc q b) (t : Tape) :
    (obsPhase q b M).halted ⟨embOb q b s, t⟩ = false := by
  rw [DTM.halted, Bool.or_eq_false_iff]
  refine ⟨beq_eq_false_iff_ne.mpr ?_, beq_eq_false_iff_ne.mpr ?_⟩
  · intro hh
    have hv : (embOb q b s).val = (embOb q b (obsAcc q b)).val := congrArg Fin.val hh
    exact hne (Fin.ext hv)
  · intro hh
    have hv : s.val = stateCountO q b := congrArg Fin.val hh
    have hs : s.val < stateCountO q b := s.isLt
    omega

/-- **单步的公共展开**：`embOb` 状态上 `obsPhase` 的 `if hE` 前段。
    Shared unfolding: the `if hE` prefix at an embedded state. -/
theorem obsPhase_step_emb (q b : Nat) (M : NTM q) (s : Fin (stateCountO q b)) (a : Sym) :
    (obsPhase q b M).step (embOb q b s) a =
      (let r := (simObs q b M).step s a
       if hr : r.1 = obsFail q b then (obsEsc q b, a, Dir.stay)
       else (embOb q b r.1, r.2.1, r.2.2)) := by
  simp only [obsPhase]
  rw [dite_eq_left (show (embOb q b s).val < stateCountO q b from s.isLt)]
  rw [show (⟨(embOb q b s).val, _⟩ : Fin (stateCountO q b)) = s from Fin.ext rfl]

/-- **照抄单步**：若 `simObs` 的一步不落进失败哨兵，则 `obsPhase` 走同一步。
    One-step copy: if `simObs`'s step does not land on the fail sentinel, `obsPhase` copies it. -/
theorem obsPhase_step_copy (q b : Nat) (M : NTM q) (s : Fin (stateCountO q b)) (a : Sym)
    (hne : ((simObs q b M).step s a).1 ≠ obsFail q b) :
    (obsPhase q b M).step (embOb q b s) a
      = (embOb q b ((simObs q b M).step s a).1, ((simObs q b M).step s a).2) := by
  rw [obsPhase_step_emb]
  dsimp only
  rw [dite_eq_right hne]

/-- **改接单步**：若 `simObs` 的一步落进失败哨兵，则 `obsPhase` 进入逃生态。
    One-step redirect: if `simObs`'s step lands on the fail sentinel, `obsPhase` escapes. -/
theorem obsPhase_step_escape (q b : Nat) (M : NTM q) (s : Fin (stateCountO q b)) (a : Sym)
    (heq : ((simObs q b M).step s a).1 = obsFail q b) :
    (obsPhase q b M).step (embOb q b s) a = (obsEsc q b, a, Dir.stay) := by
  rw [obsPhase_step_emb]
  dsimp only
  rw [dite_eq_left heq]

/-- **照抄一步格局**：`stepConfig` 层面的单步搬运。
    One-step `stepConfig` copy. -/
theorem obsPhase_stepConfig_copy (q b : Nat) (M : NTM q) (c : Config (stateCountO q b))
    (hne : ((simObs q b M).step c.state c.tape.read).1 ≠ obsFail q b) :
    (obsPhase q b M).stepConfig ⟨embOb q b c.state, c.tape⟩ =
      ⟨embOb q b ((simObs q b M).stepConfig c).state,
        ((simObs q b M).stepConfig c).tape⟩ := by
  unfold DTM.stepConfig
  rw [obsPhase_step_copy q b M c.state c.tape.read hne]

/-- **前缀无哨兵 ⇒ 照抄整段**：`simObs` 前 `n` 步（不含第 `n` 步）都在非哨兵状态、且第 `n` 步
    也不是失败哨兵，则 `obsPhase` 跑同样 `n` 步得到嵌入后的同一格局。
    Whole-run copy: if no sentinel occurs among the first `n` states and the `n`-th state is
    not the fail sentinel either, `obsPhase` copies the run. -/
theorem obsPhase_run_copy (q b : Nat) (M : NTM q) :
    ∀ (n : Nat) (c : Config (stateCountO q b)),
      (∀ m, m < n → ((simObs q b M).run m c).state ≠ obsAcc q b ∧
                     ((simObs q b M).run m c).state ≠ obsFail q b) →
      ((simObs q b M).run n c).state ≠ obsFail q b →
      (obsPhase q b M).run n ⟨embOb q b c.state, c.tape⟩ =
        ⟨embOb q b ((simObs q b M).run n c).state, ((simObs q b M).run n c).tape⟩ := by
  intro n
  induction n with
  | zero =>
      intro c _ _
      rfl
  | succ n ih =>
      intro c hpre hfin
      have hpre' : ∀ m, m < n → ((simObs q b M).run m c).state ≠ obsAcc q b ∧
          ((simObs q b M).run m c).state ≠ obsFail q b := fun m hm => hpre m (by omega)
      have hn1 : ((simObs q b M).run n c).state ≠ obsAcc q b := (hpre n (by omega)).1
      have hfin' : ((simObs q b M).run n c).state ≠ obsFail q b := (hpre n (by omega)).2
      -- 第 n 步的转移结果不是失败哨兵（否则第 n+1 步的状态就是失败哨兵）
      have hstep : ((simObs q b M).step ((simObs q b M).run n c).state
          ((simObs q b M).run n c).tape.read).1 ≠ obsFail q b := by
        intro hh
        have hnot : (simObs q b M).halted ((simObs q b M).run n c) = false :=
          simObs_halted_of_ne q b M _ hn1 hfin'
        have hstate : ((simObs q b M).run (n + 1) c).state = obsFail q b := by
          rw [run_succ_last (simObs q b M) n c hnot, stepConfig_state]
          exact hh
        exact hfin hstate
      rw [DTM.run_add (obsPhase q b M) n 1, ih c hpre' hfin']
      show (obsPhase q b M).run (0 + 1)
          ⟨embOb q b ((simObs q b M).run n c).state, ((simObs q b M).run n c).tape⟩
        = ⟨embOb q b ((simObs q b M).run (n + 1) c).state,
            ((simObs q b M).run (n + 1) c).tape⟩
      rw [DTM.run_succ_of_not_halted (obsPhase q b M) 0 _
        (obsPhase_halted_inner q b M _ hn1 _)]
      rw [run_succ_last (simObs q b M) n c
        (simObs_halted_of_ne q b M _ hn1 hfin')]
      exact obsPhase_stepConfig_copy q b M ((simObs q b M).run n c) hstep

/-- **第 n 步进入失败哨兵 ⇒ 第 n+1 步到逃生态**（纸带右侧非空以保证原位保持）。
    Escape: if `simObs`'s `n`-th step lands on the fail sentinel, `obsPhase` reaches the
    escape state in `n+1` steps, leaving the tape unchanged. -/
theorem obsPhase_run_escape (q b : Nat) (M : NTM q) :
    ∀ (n : Nat) (c : Config (stateCountO q b)),
      (∀ m, m ≤ n → ((simObs q b M).run m c).state ≠ obsAcc q b ∧
                     ((simObs q b M).run m c).state ≠ obsFail q b) →
      ((simObs q b M).step ((simObs q b M).run n c).state
        ((simObs q b M).run n c).tape.read).1 = obsFail q b →
      ((simObs q b M).run n c).tape.right ≠ [] →
      (obsPhase q b M).run (n + 1) ⟨embOb q b c.state, c.tape⟩ =
        ⟨obsEsc q b, ((simObs q b M).run n c).tape⟩ := by
  intro n c hpre heq hr
  have hn1 : ((simObs q b M).run n c).state ≠ obsAcc q b := (hpre n (Nat.le_refl n)).1
  have hfin : ((simObs q b M).run n c).state ≠ obsFail q b := (hpre n (Nat.le_refl n)).2
  have hcopy := obsPhase_run_copy q b M n c
    (fun m hm => hpre m (Nat.le_of_lt hm)) hfin
  rw [DTM.run_add (obsPhase q b M) n 1, hcopy]
  show (obsPhase q b M).run (0 + 1)
      ⟨embOb q b ((simObs q b M).run n c).state, ((simObs q b M).run n c).tape⟩
    = ⟨obsEsc q b, ((simObs q b M).run n c).tape⟩
  rw [DTM.run_succ_of_not_halted (obsPhase q b M) 0 _
    (obsPhase_halted_inner q b M _ hn1 _)]
  unfold DTM.stepConfig
  rw [obsPhase_step_escape q b M _ ((simObs q b M).run n c).tape.read heq]
  dsimp only
  rw [show (((simObs q b M).run n c).tape.write ((simObs q b M).run n c).tape.read).move
        Dir.stay = ((simObs q b M).run n c).tape.write ((simObs q b M).run n c).tape.read
      from rfl, Tape.write_read _ hr]
  rfl

/-! ## 预算层桥接：`simObs` 的终点决定 `obsPhase` 的终点 -/

/-- 失败哨兵与接受哨兵不同。 The fail and accept sentinels differ. -/
theorem obsFail_ne_obsAccO (q b : Nat) : obsFail q b ≠ obsAcc q b := by
  intro hh
  have hv := congrArg Fin.val hh
  rw [show (obsFail q b).val = stateCountD q b + 1 from rfl,
    show (obsAcc q b).val = stateCountD q b from rfl] at hv
  omega

/-- 哨兵状态（状态号 ≥ 驱动空间）上 `simObs` 原地停留。
    On a sentinel state `simObs` stays put. -/
theorem simObs_step_outer (q b : Nat) (M : NTM q) (s : Fin (stateCountO q b))
    (hge : ¬ s.val < stateCountD q b) (a : Sym) :
    (simObs q b M).step s a = (s, a, Dir.stay) := by
  simp only [simObs]
  rw [dite_eq_right hge]

/-- 失败哨兵上的单步：状态仍是失败哨兵。 The fail sentinel is fixed by its own step. -/
theorem simObs_fail_step_fst (q b : Nat) (M : NTM q) (a : Sym) :
    ((simObs q b M).step (obsFail q b) a).1 = obsFail q b := by
  rw [simObs_step_outer q b M (obsFail q b)
    (by show ¬ (stateCountD q b + 1 < stateCountD q b); omega)]

/-- 逃生态是停机态（拒绝）。 The escape state halts (reject). -/
theorem obsPhase_halted_esc (q b : Nat) (M : NTM q) (t : Tape) :
    (obsPhase q b M).halted ⟨obsEsc q b, t⟩ = true :=
  halted_of_accept_or_reject (obsPhase q b M) _ (Or.inr rfl)

/-- **逃逸一步后冻结**：若格局已在失败哨兵处，则 `obsPhase` 在 `n+1` 步后停在逃生态，
    纸带为「写入原符号并停留」后的形态（无需右侧非空前提）。
    Escaping then freezing: from a config at the fail sentinel, `obsPhase` sits at the escape
    state after `n+1` steps, with the unchanged-write tape form. -/
theorem obsPhase_escape_once (q b : Nat) (M : NTM q) (c : Config (stateCountO q b))
    (hc : c.state = obsFail q b) (n : Nat) :
    (obsPhase q b M).run (n + 1) ⟨embOb q b c.state, c.tape⟩ =
      ⟨obsEsc q b, (c.tape.write c.tape.read).move Dir.stay⟩ := by
  have hnhO : (obsPhase q b M).halted ⟨embOb q b c.state, c.tape⟩ = false := by
    refine obsPhase_halted_inner q b M c.state ?_ c.tape
    intro hacc
    exact obsFail_ne_obsAccO q b (hc.symm.trans hacc)
  have hone : (obsPhase q b M).run 1 ⟨embOb q b c.state, c.tape⟩ =
      ⟨obsEsc q b, (c.tape.write c.tape.read).move Dir.stay⟩ := by
    show (obsPhase q b M).run (0 + 1)
        ⟨embOb q b c.state, c.tape⟩
      = ⟨obsEsc q b, (c.tape.write c.tape.read).move Dir.stay⟩
    rw [DTM.run_succ_of_not_halted (obsPhase q b M) 0 _ hnhO]
    unfold DTM.stepConfig
    rw [obsPhase_step_escape q b M c.state c.tape.read
      (by rw [hc]; exact simObs_fail_step_fst q b M c.tape.read)]
    dsimp only
    rfl
  rw [show n + 1 = 1 + n from Nat.add_comm n 1, DTM.run_add (obsPhase q b M) 1 n, hone]
  exact run_of_halted (obsPhase q b M) _ (obsPhase_halted_esc q b M _) n

/-- **预算内接受 ⇒ 运行相位机接受**：`simObs` 跑 `K` 步停在接受哨兵 ⇒ `obsPhase`
    同样跑 `K` 步停在接受态，纸带相同。
    Budget accept: if `simObs` ends at the accept sentinel after `K` steps, so does `obsPhase`
    (same tape). -/
theorem obsPhase_budget_accept (q b : Nat) (M : NTM q) :
    ∀ (K : Nat) (c : Config (stateCountO q b)),
      ((simObs q b M).run K c).state = obsAcc q b →
      (obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩ =
        ⟨embOb q b (obsAcc q b), ((simObs q b M).run K c).tape⟩ := by
  intro K
  induction K with
  | zero =>
      intro c h
      rw [show (simObs q b M).run 0 c = c from rfl] at h
      rw [h]
      rfl
  | succ K ih =>
      intro c h
      by_cases hh : (simObs q b M).halted c = true
      · -- 已停机：两边都冻结在 `c`
        have hc : c.state = obsAcc q b := by
          rw [run_of_halted (simObs q b M) c hh] at h
          exact h
        have hO : (obsPhase q b M).halted ⟨embOb q b c.state, c.tape⟩ = true := by
          rw [hc]
          exact halted_of_accept_or_reject (obsPhase q b M) _ (Or.inl rfl)
        rw [run_of_halted (simObs q b M) c hh,
          run_of_halted (obsPhase q b M) ⟨embOb q b c.state, c.tape⟩ hO, hc]
      · have hnh : (simObs q b M).halted c = false := by
          cases hv : (simObs q b M).halted c with
          | false => rfl
          | true => exact absurd hv hh
        have hK : ((simObs q b M).run (K + 1) c).state =
            ((simObs q b M).run K ((simObs q b M).stepConfig c)).state := by
          rw [DTM.run_succ_of_not_halted (simObs q b M) K c hnh]
        -- 第 K 步的转移结果不是失败哨兵（否则终点状态是失败哨兵）
        have hstep : ((simObs q b M).step c.state c.tape.read).1 ≠ obsFail q b := by
          intro heq
          have hst : ((simObs q b M).stepConfig c).state = obsFail q b := by
            rw [stepConfig_state]
            exact heq
          have hnot : (simObs q b M).halted ((simObs q b M).stepConfig c) = true :=
            halted_of_accept_or_reject (simObs q b M) _ (Or.inr hst)
          have hcontra : ((simObs q b M).run K ((simObs q b M).stepConfig c)).state
              = obsFail q b := by
            rw [run_of_halted (simObs q b M) _ hnot]
            exact hst
          exact obsFail_ne_obsAccO q b (hcontra.symm.trans (hK ▸ h))
        have hnhO : (obsPhase q b M).halted ⟨embOb q b c.state, c.tape⟩ = false := by
          refine obsPhase_halted_inner q b M c.state ?_ c.tape
          intro hacc
          exact hh (halted_of_accept_or_reject (simObs q b M) c (Or.inl hacc))
        rw [DTM.run_succ_of_not_halted (simObs q b M) K c hnh,
          DTM.run_succ_of_not_halted (obsPhase q b M) K ⟨embOb q b c.state, c.tape⟩ hnhO,
          obsPhase_stepConfig_copy q b M c hstep]
        exact ih ((simObs q b M).stepConfig c) (hK ▸ h)

/-- **格局投影**：`obsPhase` 第 `K` 步的格局要么与 `simObs` 完全一致（状态嵌入、纸带相同），
    要么已逃逸（此时 `simObs` 停在失败哨兵）。
    Config projection: after `K` steps `obsPhase` either matches `simObs` exactly (embedded
    state, same tape) or has escaped — and escaping only happens once `simObs` sits at the
    fail sentinel. -/
theorem obsPhase_run_config_proj (q b : Nat) (M : NTM q) :
    ∀ (K : Nat) (c : Config (stateCountO q b)),
      (obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩
          = ⟨embOb q b ((simObs q b M).run K c).state, ((simObs q b M).run K c).tape⟩
      ∨ (((obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩).state = obsEsc q b ∧
         ((simObs q b M).run K c).state = obsFail q b) := by
  intro K
  induction K with
  | zero =>
      intro c
      exact Or.inl rfl
  | succ K ih =>
      intro c
      rcases ih c with hleft | ⟨hright, hfailK⟩
      · by_cases hacc : ((simObs q b M).run K c).state = obsAcc q b
        · -- 接受哨兵：两边冻结
          have hs : (simObs q b M).run (K + 1) c = (simObs q b M).run K c :=
            DTM.run_add (simObs q b M) K 1 c ▸
              run_of_halted (simObs q b M) _ (halted_of_accept_or_reject (simObs q b M) _
                (Or.inl hacc)) 1
          have hO : (obsPhase q b M).halted
              ((obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩) = true := by
            rw [hleft]
            exact halted_of_accept_or_reject (obsPhase q b M) _
              (Or.inl (by rw [hacc]; rfl))
          have ho : (obsPhase q b M).run (K + 1) ⟨embOb q b c.state, c.tape⟩ =
              (obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩ :=
            DTM.run_add (obsPhase q b M) K 1 _ ▸
              run_of_halted (obsPhase q b M) _ hO 1
          rw [ho, hs]
          exact Or.inl hleft
        · by_cases hfail : ((simObs q b M).run K c).state = obsFail q b
          · -- 失败哨兵：一步逃逸
            have hnhO : (obsPhase q b M).halted
                ((obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩) = false := by
              rw [hleft]
              exact obsPhase_halted_inner q b M _ (by rw [hfail]; exact obsFail_ne_obsAccO q b) _
            have hesc : (obsPhase q b M).run 1
                ((obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩) =
                ⟨obsEsc q b, (((simObs q b M).run K c).tape.write
                  ((simObs q b M).run K c).tape.read).move Dir.stay⟩ := by
              show (obsPhase q b M).run (0 + 1) _ = _
              rw [DTM.run_succ_of_not_halted (obsPhase q b M) 0 _ hnhO]
              unfold DTM.stepConfig
              rw [hleft, obsPhase_step_escape q b M _ _
                (by rw [hfail]; exact simObs_fail_step_fst q b M _)]
              dsimp only
              rfl
            have hs : (simObs q b M).run (K + 1) c = (simObs q b M).run K c :=
              DTM.run_add (simObs q b M) K 1 c ▸
                run_of_halted (simObs q b M) _ (halted_of_accept_or_reject (simObs q b M) _
                  (Or.inr hfail)) 1
            rw [DTM.run_add (obsPhase q b M) K 1, hesc, hs]
            exact Or.inr ⟨rfl, hfail⟩
          · -- 普通状态：一步照抄或一步逃逸
            have hnhS : (simObs q b M).halted ((simObs q b M).run K c) = false :=
              simObs_halted_of_ne q b M _ hacc hfail
            have hs : (simObs q b M).run (K + 1) c =
                (simObs q b M).stepConfig ((simObs q b M).run K c) :=
              run_succ_last (simObs q b M) K c hnhS
            have hnhO : (obsPhase q b M).halted
                ((obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩) = false := by
              rw [hleft]
              exact obsPhase_halted_inner q b M _ hacc _
            by_cases heq : ((simObs q b M).step ((simObs q b M).run K c).state
                ((simObs q b M).run K c).tape.read).1 = obsFail q b
            · have hesc : (obsPhase q b M).run 1
                  ((obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩) =
                  ⟨obsEsc q b, (((simObs q b M).run K c).tape.write
                    ((simObs q b M).run K c).tape.read).move Dir.stay⟩ := by
                show (obsPhase q b M).run (0 + 1) _ = _
                rw [DTM.run_succ_of_not_halted (obsPhase q b M) 0 _ hnhO]
                unfold DTM.stepConfig
                rw [hleft, obsPhase_step_escape q b M _ _ heq]
                dsimp only
                rfl
              have hs2 : ((simObs q b M).run (K + 1) c).state = obsFail q b := by
                rw [hs, stepConfig_state]
                exact heq
              rw [DTM.run_add (obsPhase q b M) K 1, hesc]
              exact Or.inr ⟨rfl, hs2⟩
            · have hcopy := obsPhase_stepConfig_copy q b M ((simObs q b M).run K c) heq
              have hone : (obsPhase q b M).run 1
                  ((obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩) =
                  (obsPhase q b M).stepConfig
                    ((obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩) := by
                show (obsPhase q b M).run (0 + 1) _ = _
                rw [DTM.run_succ_of_not_halted (obsPhase q b M) 0 _ hnhO]
                rfl
              rw [DTM.run_add (obsPhase q b M) K 1, hone, hleft, hcopy, hs]
              exact Or.inl rfl
      · -- 已逃逸：逃生态停机，永不离开
        have hO : (obsPhase q b M).halted
            ((obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩) = true :=
          halted_of_accept_or_reject (obsPhase q b M) _ (Or.inr (by rw [hright]; rfl))
        have ho : (obsPhase q b M).run (K + 1) ⟨embOb q b c.state, c.tape⟩ =
            (obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩ :=
          DTM.run_add (obsPhase q b M) K 1 _ ▸ run_of_halted (obsPhase q b M) _ hO 1
        have hs : ((simObs q b M).run (K + 1) c).state = obsFail q b := by
          rw [DTM.run_add (simObs q b M) K 1,
            run_of_halted (simObs q b M) _
              (halted_of_accept_or_reject (simObs q b M) _ (Or.inr hfailK))]
          exact hfailK
        rw [ho, hs]
        exact Or.inr ⟨hright, rfl⟩

/-- **接受 ⇔ 观察机接受**（预算层）：`obsPhase` 跑 `K` 步停在接受态，当且仅当 `simObs`
    跑 `K` 步停在接受哨兵。
    Budget-level equivalence: `obsPhase` accepts after `K` steps iff `simObs` does. -/
theorem obsPhase_accept_iff (q b : Nat) (M : NTM q) (K : Nat)
    (c : Config (stateCountO q b)) :
    ((obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩).state
        = (obsPhase q b M).accept
      ↔ ((simObs q b M).run K c).state = obsAcc q b := by
  constructor
  · intro h
    rcases obsPhase_run_config_proj q b M K c with hl | ⟨hr, _⟩
    · have hst : ((obsPhase q b M).run K ⟨embOb q b c.state, c.tape⟩).state
          = embOb q b ((simObs q b M).run K c).state := congrArg Config.state hl
      have hv : embOb q b ((simObs q b M).run K c).state = (obsPhase q b M).accept :=
        hst.symm.trans h
      have hv2 := congrArg Fin.val hv
      have hv3 : ((simObs q b M).run K c).state.val = (obsAcc q b).val := hv2
      exact Fin.ext hv3
    · exfalso
      rw [hr] at h
      have hv := congrArg Fin.val h
      rw [show (obsEsc q b).val = stateCountO q b from rfl,
        show (obsPhase q b M).accept.val = stateCountD q b from rfl] at hv
      unfold stateCountO at hv
      omega
  · intro h
    rcases obsPhase_run_config_proj q b M K c with hl | ⟨hr, hf⟩
    · rw [hl, h]
      rfl
    · exfalso
      rw [h] at hf
      exact obsFail_ne_obsAccO q b hf.symm

end DTM

end Pnp
