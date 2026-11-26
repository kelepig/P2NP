/-
  文件：Pnp/Machine/SimPassRev.lean
  主题：通路的**完备性**（反向桥接）——只要每个选择编号都 ≥ 1（占位机的形态），
        区域按选择序列迭代成功，就一定存在一个成功的通路，并且通路终态区域
        正是该迭代结果。

  用途（B5 反向方向）：给定原机 `M` 的一条 `T` 步接受运行，把选择序列整体 +1
  交给占位机 `M.stutter`（每个编号 ≥ 1，符合数字区「块值 `k` ⇒ 下一轮选择 `k + 1``
  的语义），本文件保证对应的通路会走通，从而外层枚举有机会命中该分支
  （auto-run-log #113/#114）。

  Converse (completeness) bridge: if every choice index is ≥ 1, a successful
  region iteration admits a successful pass whose final region is exactly the
  iterated one.
-/

import Pnp.Machine.SimPass

set_option maxHeartbeats 800000

namespace Pnp

namespace DTM

/-- 选择序列其余项逐项减 1、末尾补一个哑元数字后，其通路选择序列正好还原原序列。
    最后一块的数字值不被使用（`passChoices` 长度 = 块数），故需要哑元占位。
    Subtracting 1 from the tail entries and appending one dummy digit recovers the
    original choice sequence (the last block's value is unused). -/
theorem passChoices_map_pred_append :
    ∀ (dummy : Nat) (ds : List Nat), (∀ x ∈ ds, 1 ≤ x) →
      ∀ (c : Nat), passChoices c (ds.map (fun x => x - 1) ++ [dummy]) = c :: ds := by
  intro dummy ds
  induction ds with
  | nil => intro _ c; rfl
  | cons d ds ih =>
      intro hpos c
      have hd : 1 ≤ d := hpos d (by simp)
      have hds : ∀ x ∈ ds, 1 ≤ x := fun x hx => hpos x (by simp [hx])
      simp only [List.map_cons, List.cons_append, passChoices]
      rw [show d - 1 + 1 = d from by omega, ih hds d]

/-- **通路完备性**：区域按选择列表（规范形）迭代成功 ⇒ 通路成功，且终态区域相同。
    Pass completeness: a successful canonical region iteration yields a successful
    pass with the same final region. -/
theorem exists_passRun_of_stepCs (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    ∀ (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x y : Reg q)
      (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b),
      stepCs tab (passChoices c L) x = some y →
      ∃ r : PassRes q b, passRun q b tab Z c hc x L hb = some r ∧ r.reg = y := by
  intro L
  induction L with
  | nil =>
      intro Z c hc x y hb h
      simp only [passChoices, stepCs, Option.some.injEq] at h
      subst h
      exact ⟨⟨0, Z, c, hc, x⟩, rfl, rfl⟩
  | cons k ks ih =>
      intro Z c hc x y hb h
      simp only [passChoices, stepCs] at h
      have hc' : k + 1 < 2 ^ b := by
        have := hb k (by simp)
        omega
      have hb' : ∀ k' ∈ ks, k' + 2 < 2 ^ b :=
        fun k' hk' => hb k' (by simp [hk'])
      cases hstep : Reg.step tab c x with
      | none =>
          rw [hstep] at h
          have h2 : (none : Option (Reg q)) = some y := h
          cases h2
      | some x' =>
          rw [hstep] at h
          have h' : stepCs tab (passChoices (k + 1) ks) x' = some y := h
          -- 按候选动作与方向确定后继区域的具体形状
          cases hpick : pick (tab x.state x.cur) c with
          | none =>
              simp only [Reg.step, hpick] at hstep
              cases hstep
          | some v =>
              obtain ⟨m', s', d⟩ := v
              cases d with
              | stay =>
                  simp only [Reg.step, hpick, Option.some.injEq] at hstep
                  cases hstep
                  obtain ⟨r, hpass, hreg⟩ := ih (Z + k + 3) (k + 1) hc'
                    { state := m', pre := x.pre, cur := s', post := x.post } y hb' h'
                  rw [passRun_stay_unfold q b tab Z c hc x k ks hb m' s' hpick, hpass]
                  simp only [Option.map_some]
                  exact ⟨_, rfl, hreg⟩
              | right =>
                  cases hpost : x.post with
                  | nil =>
                      simp only [Reg.step, hpick, hpost] at hstep
                      cases hstep
                  | cons p post' =>
                      simp only [Reg.step, hpick, hpost, Option.some.injEq] at hstep
                      cases hstep
                      obtain ⟨r, hpass, hreg⟩ := ih (Z + k + 3) (k + 1) hc'
                        { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                        y hb' h'
                      rw [passRun_right_unfold q b tab Z c hc x k ks hb m' s' p post' hpost
                        hpick, hpass]
                      simp only [Option.map_some]
                      exact ⟨_, rfl, hreg⟩
              | left =>
                  cases hrev : x.pre.reverse with
                  | nil =>
                      simp only [Reg.step, hpick, hrev] at hstep
                      cases hstep
                  | cons cq preRev =>
                      simp only [Reg.step, hpick, hrev, Option.some.injEq] at hstep
                      cases hstep
                      obtain ⟨r, hpass, hreg⟩ := ih (Z + k + 3) (k + 1) hc'
                        { state := m', pre := preRev.reverse, cur := cq.1,
                          post := (s', false) :: x.post } y hb' h'
                      rw [passRun_left_unfold q b tab Z c hc x k ks hb m' s' cq preRev hrev
                        hpick, hpass]
                      simp only [Option.map_some]
                      exact ⟨_, rfl, hreg⟩

/-- **面向枚举的完备性**：占位机形态的选择序列（`c :: cs`，其余各项 ≥ 1）
    只要迭代成功，就以「其余各项减 1 再补哑元」作为数字区参数得到成功通路。
    Enumeration-facing completeness: a `c :: cs` run with `cs` entries ≥ 1
    corresponds to the digit list `cs.map (· - 1) ++ [dummy]`. -/
theorem exists_passRun_of_stepCs_map (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (c : Nat) (hc : c < 2 ^ b) (dummy : Nat) (hdummy : dummy + 2 < 2 ^ b)
    (cs : List Nat) (hpos : ∀ x ∈ cs, 1 ≤ x) (hbound : ∀ x ∈ cs, x + 1 < 2 ^ b)
    (Z : Nat) (x y : Reg q) (h : stepCs tab (c :: cs) x = some y) :
    ∃ r : PassRes q b,
      passRun q b tab Z c hc x (cs.map (fun x => x - 1) ++ [dummy])
        (fun k' hk' => by
          rcases List.mem_append.mp hk' with hm | hs
          · obtain ⟨d, hdmem, rfl⟩ := List.mem_map.mp hm
            have h1 := hbound d hdmem
            have h2 := hpos d hdmem
            show d - 1 + 2 < 2 ^ b
            have h3 : d - 1 + 2 = d + 1 := by omega
            omega
          · simp only [List.mem_singleton] at hs
            subst hs
            exact hdummy) = some r ∧
      r.reg = y := by
  have h2 : stepCs tab (passChoices c (cs.map (fun x => x - 1) ++ [dummy])) x = some y := by
    rwa [passChoices_map_pred_append dummy cs hpos c]
  exact exists_passRun_of_stepCs q b tab (cs.map (fun x => x - 1) ++ [dummy]) Z c hc x y _ h2

end DTM

end Pnp
