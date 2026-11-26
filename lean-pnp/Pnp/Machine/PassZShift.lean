/-
  文件：Pnp/Machine/PassZShift.lean
  File: Pnp/Machine/PassZShift.lean

  主题：通路驱动 `passRun` 对零点计数 `Z` 的平移——**成功与否与 `Z` 无关**，
  且 `Z` 增加 `d` 时终态区域、计数器不变，只有零计数 `+d`、总步数 `+2d·轮数`。
  Topic: shifting the zero count `Z` in the pass driver. Success does not depend on `Z`;
  adding `d` to `Z` keeps the final region and counter, adds `d` to the zero count and
  `2d·rounds` to the step count.

  用途（B5 逐分支入口）：哑元首轮把零计数从 `Z` 推到 `Z + k + 3`，而分支族的
  完备性定理是对某个固定 `Z` 陈述的。本文件把成功通路搬到平移后的 `Z'`，
  从而接上哑元轮的结论。
  Purpose (B5 per-branch entry): the dummy round shifts the zero count from `Z` to
  `Z + k + 3`, while completeness is stated at a fixed `Z`. This file transports a
  successful pass to the shifted `Z'` so the dummy round's result can be used.
-/

import Pnp.Machine.SimPass

namespace Pnp

namespace DTM

/-- 任一单轮步数与 `z` 的关系：`z` 每加 `d`，步数加 `2d`。 -/
theorem roundCostStay_shift {q : Nat} (x : Reg q) (z d k : Nat) (s' : Sym) :
    roundCostStay x (z + d) k s' = roundCostStay x z k s' + 2 * d := by
  unfold roundCostStay
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- 右移轮的成本平移。 -/
theorem roundCostRight_shift {q : Nat} (x : Reg q) (z d k : Nat) (p : Sym × Bool) (s' : Sym) :
    roundCostRight x (z + d) k p s' = roundCostRight x z k p s' + 2 * d := by
  unfold roundCostRight
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- 左移轮的成本平移。 -/
theorem roundCostLeft_shift {q : Nat} (z d k : Nat) (pre' : List (Sym × Bool))
    (cq : Sym × Bool) (s' : Sym) :
    roundCostLeft (q := q) (z + d) k pre' cq s' = roundCostLeft (q := q) z k pre' cq s' + 2 * d := by
  unfold roundCostLeft
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- **通路驱动对 `Z` 的平移**：若 `Z` 下通路成功并得到 `r`，则 `Z + d` 下也成功，
    终态区域与计数器不变，零计数 `+d`，总步数 `+2d·轮数`。
    Pass driver shift in `Z`: success transports, the region and the counter are
    unchanged, the zero count grows by `d`, and the step count by `2d·rounds`. -/
theorem passRun_z_shift (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (ks : List Nat) :
    ∀ (Z d c : Nat) (hc : c < 2 ^ b) (x : Reg q)
      (hb : ∀ k' ∈ ks, k' + 2 < 2 ^ b) (r : PassRes q b),
      passRun q b tab Z c hc x ks hb = some r →
      ∃ r', passRun q b tab (Z + d) c hc x ks hb = some r' ∧
        r'.reg = r.reg ∧ r'.c = r.c ∧ r'.z = r.z + d ∧
        r'.steps = r.steps + 2 * d * ks.length := by
  induction ks with
  | nil =>
      intro Z d c hc x hb r h
      -- 空数字区：直接给出初始结果
      simp only [passRun, Option.some.injEq] at h
      subst h
      exact ⟨⟨0, Z + d, c, hc, x⟩, rfl, rfl, rfl, by simp, by simp⟩
  | cons k ks ih =>
      intro Z d c hc x hb r h
      cases hpk : pick (tab x.state x.cur) c with
      | none =>
          rw [passRun_none_unfold q b tab Z c hc x k ks hb hpk] at h
          exact absurd h (by simp)
      | some t =>
          obtain ⟨m', s', dir⟩ := t
          cases dir with
          | stay =>
              rw [passRun_stay_unfold q b tab Z c hc x k ks hb m' s' hpk] at h
              cases h2 : passRun q b tab (Z + k + 3) (k + 1)
                  (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                  { state := m', pre := x.pre, cur := s', post := x.post } ks
                  (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
              | none => rw [h2] at h; simp at h
              | some r1 =>
                  rw [h2] at h
                  simp only [Option.map, Option.some.injEq] at h
                  subst h
                  obtain ⟨r1', hr1', hreg, hc', hz, hst⟩ :=
                    ih (Z + k + 3) d (k + 1) _
                      { state := m', pre := x.pre, cur := s', post := x.post } _ r1 h2
                  refine ⟨⟨roundCostStay x (Z + d) k s' + r1'.steps, r1'.z, r1'.c,
                    r1'.hc, r1'.reg⟩, ?_, hreg, hc', hz, ?_⟩
                  · rw [passRun_stay_unfold q b tab (Z + d) c hc x k ks hb m' s' hpk]
                    rw [show Z + d + k + 3 = Z + k + 3 + d from by omega, hr1']
                    rfl
                  · rw [roundCostStay_shift, hst]
                    simp only [List.length_cons]
                    rw [Nat.mul_add, Nat.mul_one]
                    omega
          | right =>
              cases hp : x.post with
              | nil =>
                  rw [passRun_right_nil_unfold q b tab Z c hc x k ks hb m' s' hp hpk] at h
                  exact absurd h (by simp)
              | cons p post' =>
                  rw [passRun_right_unfold q b tab Z c hc x k ks hb m' s' p post' hp hpk] at h
                  cases h2 : passRun q b tab (Z + k + 3) (k + 1)
                      (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                      { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } ks
                      (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
                  | none => rw [h2] at h; simp at h
                  | some r1 =>
                      rw [h2] at h
                      simp only [Option.map, Option.some.injEq] at h
                      subst h
                      obtain ⟨r1', hr1', hreg, hc', hz, hst⟩ :=
                        ih (Z + k + 3) d (k + 1) _
                          { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                          _ r1 h2
                      refine ⟨⟨roundCostRight x (Z + d) k p s' + r1'.steps, r1'.z, r1'.c,
                        r1'.hc, r1'.reg⟩, ?_, hreg, hc', hz, ?_⟩
                      · rw [passRun_right_unfold q b tab (Z + d) c hc x k ks hb m' s' p post'
                          hp hpk]
                        rw [show Z + d + k + 3 = Z + k + 3 + d from by omega, hr1']
                        rfl
                      · rw [roundCostRight_shift, hst]
                        simp only [List.length_cons]
                        rw [Nat.mul_add, Nat.mul_one]
                        omega
          | left =>
              cases hp : x.pre.reverse with
              | nil =>
                  rw [passRun_left_nil_unfold q b tab Z c hc x k ks hb m' s' hp hpk] at h
                  exact absurd h (by simp)
              | cons cq preRev =>
                  rw [passRun_left_unfold q b tab Z c hc x k ks hb m' s' cq preRev hp hpk] at h
                  cases h2 : passRun q b tab (Z + k + 3) (k + 1)
                      (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                      { state := m', pre := preRev.reverse, cur := cq.1,
                        post := (s', false) :: x.post } ks
                      (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
                  | none => rw [h2] at h; simp at h
                  | some r1 =>
                      rw [h2] at h
                      simp only [Option.map, Option.some.injEq] at h
                      subst h
                      obtain ⟨r1', hr1', hreg, hc', hz, hst⟩ :=
                        ih (Z + k + 3) d (k + 1) _
                          { state := m', pre := preRev.reverse, cur := cq.1,
                            post := (s', false) :: x.post } _ r1 h2
                      refine ⟨⟨roundCostLeft (q := q) (Z + d) k preRev.reverse cq s'
                          + r1'.steps, r1'.z, r1'.c, r1'.hc, r1'.reg⟩, ?_, hreg, hc', hz, ?_⟩
                      · rw [passRun_left_unfold q b tab (Z + d) c hc x k ks hb m' s' cq preRev
                          hp hpk]
                        rw [show Z + d + k + 3 = Z + k + 3 + d from by omega, hr1']
                        rfl
                      · rw [roundCostLeft_shift, hst]
                        simp only [List.length_cons]
                        rw [Nat.mul_add, Nat.mul_one]
                        omega

end DTM

end Pnp
