/-
  文件：Pnp/Machine/SimVerdict.lean
  主题：分支判定的语义桥——把「区域层通路成功且终态接受」翻译回
        「原非确定机在 T 步内接受」，为外层枚举的正确性提供单向（接受方向）桥接。

  背景（docs/decisions/auto-run-log.md #89 / #91）：
    - 外层机器模拟的是规范形 `M.haltNorm`（接受 / 拒绝态候选动作清空），
      它在语义上与 `M` 等价（`haltNorm_acceptsWithin`）；
    - `passRun_reg`：通路成功 ⇒ 区域按 `passChoices` 逐步 `Reg.step` 到终态；
    - 本文件补上「`Reg.step` 迭代 ⇒ `runWith`」与由此得到的接受语义。

  Semantic bridge for one branch: a successful pass ending in the accept state
  implies that the simulated NTM accepts within T.
-/

import Pnp.Machine.SimPass

namespace Pnp

namespace DTM

/-- 选择列表长度在 `passChoices` 下保持不变。 -/
theorem passChoices_length (c : Nat) :
    ∀ (L : List Nat), (passChoices c L).length = L.length
  | [] => rfl
  | k :: ks => by
      simp only [passChoices, List.length_cons, passChoices_length (k + 1) ks]

/-- 停机态在规范形下没有候选动作，故任何选择编号都查表失败。 -/
theorem pick_haltNorm_none (M : NTM q) (x : Reg q) (c : Nat)
    (h : x.state = M.accept ∨ x.state = M.reject) :
    pick ((M.haltNorm).step x.state x.cur) c = none := by
  simp only [NTM.haltNorm]
  rw [if_pos h]
  cases c <;> rfl

/-- 停机判断为真时状态必是接受或拒绝（`halted` 的反向刻画）。 -/
theorem state_accept_or_reject_of_halted (M : NTM q) (c : Config q)
    (h : M.halted c = true) : c.state = M.accept ∨ c.state = M.reject := by
  rw [NTM.halted] at h
  simp only [Bool.or_eq_true, beq_iff_eq] at h
  exact h

/-- **区域迭代 ⇒ `runWith`**（规范形）：区域按选择列表逐步成功，
    则 `runWith` 沿同一列表到达对应格局。
    Region iteration implies `runWith` under the halt normal form. -/
theorem runWith_of_stepCs (M : NTM q) :
    ∀ (cs : List Nat) (x y : Reg q), x.MarkersOK →
      stepCs (M.haltNorm).step cs x = some y →
      (M.haltNorm).runWith cs.length cs x.toConfig = some y.toConfig := by
  intro cs
  induction cs with
  | nil =>
      intro x y _ h
      simp only [stepCs, Option.some.injEq] at h
      subst h
      simp only [List.length_nil, NTM.runWith]
  | cons c cs ih =>
      intro x y hx h
      simp only [stepCs] at h
      cases hs : Reg.step (M.haltNorm).step c x with
      | none =>
          rw [hs] at h
          exact absurd h (by simp)
      | some z =>
          rw [hs, Option.bind_some] at h
          -- 起点未停机（否则查表必失败，与 `hs` 矛盾）
          have hnh : (M.haltNorm).halted x.toConfig = false := by
            cases hh : (M.haltNorm).halted x.toConfig with
            | false => rfl
            | true =>
                have hst := state_accept_or_reject_of_halted M x.toConfig hh
                have hnone : Reg.step (M.haltNorm).step c x = none := by
                  rw [Reg.step, pick_haltNorm_none M x c hst]
                rw [hs] at hnone
                exact absurd hnone (by simp)
          have hz := stepWith_of_step M.haltNorm x z c hx hs
          have hzok := Reg.step_markers hs hx
          rw [List.length_cons, NTM.runWith_succ, hnh]
          simp only [hz, Option.bind_some]
          exact ih z y hzok h

/-- **分支接受 ⇒ NTM 接受**：规范形下通路成功且终态为接受态时，
    原非确定机在输入 `w` 上 `T` 步内接受。
    A successful pass ending in the accept state implies `M.AcceptsWithin w T`. -/
theorem acceptsWithin_of_passRun_accept (q b : Nat) (M : NTM q)
    (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) (r : PassRes q b)
    (w : List Bool) (T : Nat)
    (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w)) (hlen : L.length ≤ T)
    (hpass : passRun q b (M.haltNorm).step Z c hc x L hb = some r)
    (hacc : r.reg.state = M.accept) :
    M.AcceptsWithin w T := by
  have hreg := passRun_reg q b (M.haltNorm).step L c Z hc x hb r hpass
  have hlen' : (passChoices c L).length ≤ T := by
    rw [passChoices_length]
    exact hlen
  have hrun := runWith_of_stepCs M (passChoices c L) x r.reg hx hreg
  -- 空白预留不改变运行：把区域侧的规范形运行搬到 `M.init w` 侧
  obtain ⟨c2, hrun2, hst⟩ :=
    NTM.runWith_cfgEquiv (M.haltNorm) (passChoices c L).length (passChoices c L)
      hxw r.reg.toConfig hrun
  have hacc2 : c2.state = (M.haltNorm).accept := by rw [← hst]; exact hacc
  have hhalt : (M.haltNorm).halted c2 = true := by
    simp [NTM.halted, hacc2]
  have hrun' := NTM.runWith_extend (M.haltNorm) (passChoices c L).length
    (passChoices c L) (M.init w) c2 hrun2 hhalt T [] hlen'
  have hlen'' : (passChoices c L ++ []).length ≤ T := by
    rw [List.length_append, passChoices_length]
    simpa using hlen
  exact (NTM.haltNorm_acceptsWithin M w T).mp
    ⟨passChoices c L ++ [], hlen'', c2, by simpa only [NTM.init, NTM.haltNorm] using hrun', hacc2⟩

/-- **拒斥方向的必要条件**：若 `M` 在 `T` 步内不接受输入（`¬ M.AcceptsWithin w T`），
    则任何成功通路的终态区域都**不是**接受态。为外层枚举机「全部分支失败 ⇒ 拒斥」提供
    收集条件（对每条选支序列均成立）。是 `acceptsWithin_of_passRun_accept` 的逆否。
    Reject-direction necessity: if `M` does not accept `w` within `T`, no successful pass
    ends in the accepting state. Contrapositive of `acceptsWithin_of_passRun_accept`. -/
theorem passRun_not_accept_of_not_acceptsWithin (q b : Nat) (M : NTM q)
    (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) (r : PassRes q b)
    (w : List Bool) (T : Nat)
    (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w)) (hlen : L.length ≤ T)
    (hpass : passRun q b (M.haltNorm).step Z c hc x L hb = some r)
    (hna : ¬ M.AcceptsWithin w T) :
    r.reg.state ≠ M.accept := by
  intro hacc
  exact hna (acceptsWithin_of_passRun_accept q b M L Z c hc x hb r w T hx hxw hlen hpass hacc)

end DTM

end Pnp
