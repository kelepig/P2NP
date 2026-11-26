/-
  文件：Pnp/Machine/SimPassAppend.lean
  主题：通路按数字区拼接，以及「真前缀区域永不停在接受态」。

  用途（B5 反向方向 #115）：观察命中完备性需要把一整条通路拆成「前缀若干轮 + 末轮」，
  并证明前缀各轮的终态区域都不是接受态（否则 `haltNorm` 下续段查表必然失败，
  通路就不可能成功）。

  Pass concatenation along the digit area, plus the fact that no proper prefix of a
  successful pass ends in the accepting state.
-/

import Pnp.Machine.SimPassRev
import Pnp.Machine.SimRoundM

namespace Pnp

namespace DTM

/-- 通路可按数字区拼接：前缀通路与续段通路各自成功，步数相加，终态取自续段。
    A pass splits along the digit area: prefix and continuation passes, steps add up,
    and the final region comes from the continuation. -/
theorem passRun_append (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    ∀ (L1 L2 : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q)
      (hb : ∀ k' ∈ L1 ++ L2, k' + 2 < 2 ^ b) (r : PassRes q b),
      passRun q b tab Z c hc x (L1 ++ L2) hb = some r →
      ∃ (r1 r2 : PassRes q b),
        passRun q b tab Z c hc x L1
            (fun k' hk' => hb k' (List.mem_append_left L2 hk')) = some r1 ∧
        passRun q b tab r1.z r1.c r1.hc r1.reg L2
            (fun k' hk' => hb k' (List.mem_append_right L1 hk')) = some r2 ∧
        r.steps = r1.steps + r2.steps ∧ r.reg = r2.reg := by
  intro L1
  induction L1 with
  | nil =>
      intro L2 Z c hc x hb r hpass
      refine ⟨⟨0, Z, c, hc, x⟩, r, by rfl, ?_, ?_, rfl⟩
      · rw [passRun_proof_irrel q b tab L2 Z c hc x _ hb]
        exact hpass
      · show r.steps = 0 + r.steps
        omega
  | cons k ks ih =>
      intro L2 Z c hc x hb r hpass
      have hpass' : passRun q b tab Z c hc x (k :: (ks ++ L2)) hb = some r := hpass
      have hb1 : ∀ k' ∈ k :: ks, k' + 2 < 2 ^ b :=
        fun k' hk' => hb k' (List.mem_append_left L2 hk')
      have hc' : k + 1 < 2 ^ b := by
        have := hb1 k (by simp)
        omega
      cases hpick : pick (tab x.state x.cur) c with
      | none =>
          rw [passRun_none_unfold q b tab Z c hc x k (ks ++ L2) hb hpick] at hpass'
          cases hpass'
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              -- 首轮 stay：剥掉一轮后对 `ks ++ L2` 用归纳假设
              rw [passRun_stay_unfold q b tab Z c hc x k (ks ++ L2) hb m' s' hpick]
                at hpass'
              cases hp0 : passRun q b tab (Z + k + 3) (k + 1) hc'
                  { state := m', pre := x.pre, cur := s', post := x.post } (ks ++ L2) _ with
              | none =>
                  rw [hp0] at hpass'
                  cases hpass'
              | some r0 =>
                  rw [hp0] at hpass'
                  simp only [Option.map_some, Option.some.injEq] at hpass'
                  subst hpass'
                  obtain ⟨r1', r2, h1, h2, hst, hrg⟩ :=
                    ih L2 (Z + k + 3) (k + 1) hc'
                      { state := m', pre := x.pre, cur := s', post := x.post }
                      (fun k' hk' => hb k' (by simp [hk'])) r0 hp0
                  refine ⟨⟨roundCostStay x Z k s' + r1'.steps, r1'.z, r1'.c, r1'.hc,
                    r1'.reg⟩, r2, ?_, ?_, ?_, ?_⟩
                  · rw [passRun_stay_unfold q b tab Z c hc x k ks hb1 m' s' hpick]
                    rw [h1]
                    simp only [Option.map_some]
                  · exact h2
                  · dsimp only at hst ⊢
                    omega
                  · rw [hrg]
          | right =>
              cases hpost : x.post with
              | nil =>
                  simp only [passRun, hpick, hpost] at hpass'
                  cases hpass'
              | cons p post' =>
                  rw [passRun_right_unfold q b tab Z c hc x k (ks ++ L2) hb m' s' p post'
                    hpost hpick] at hpass'
                  cases hp0 : passRun q b tab (Z + k + 3) (k + 1) hc'
                      { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                      (ks ++ L2) _ with
                  | none =>
                      rw [hp0] at hpass'
                      cases hpass'
                  | some r0 =>
                      rw [hp0] at hpass'
                      simp only [Option.map_some, Option.some.injEq] at hpass'
                      subst hpass'
                      obtain ⟨r1', r2, h1, h2, hst, hrg⟩ :=
                        ih L2 (Z + k + 3) (k + 1) hc'
                          { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                          (fun k' hk' => hb k' (by simp [hk'])) r0 hp0
                      refine ⟨⟨roundCostRight x Z k p s' + r1'.steps, r1'.z, r1'.c, r1'.hc,
                        r1'.reg⟩, r2, ?_, ?_, ?_, ?_⟩
                      · rw [passRun_right_unfold q b tab Z c hc x k ks hb1 m' s' p post'
                          hpost hpick]
                        rw [h1]
                        simp only [Option.map_some]
                      · exact h2
                      · dsimp only at hst ⊢
                        omega
                      · rw [hrg]
          | left =>
              cases hrev : x.pre.reverse with
              | nil =>
                  simp only [passRun, hpick, hrev] at hpass'
                  cases hpass'
              | cons cq preRev =>
                  rw [passRun_left_unfold q b tab Z c hc x k (ks ++ L2) hb m' s' cq preRev
                    hrev hpick] at hpass'
                  cases hp0 : passRun q b tab (Z + k + 3) (k + 1) hc'
                      { state := m', pre := preRev.reverse, cur := cq.1,
                        post := (s', false) :: x.post } (ks ++ L2) _ with
                  | none =>
                      rw [hp0] at hpass'
                      cases hpass'
                  | some r0 =>
                      rw [hp0] at hpass'
                      simp only [Option.map_some, Option.some.injEq] at hpass'
                      subst hpass'
                      obtain ⟨r1', r2, h1, h2, hst, hrg⟩ :=
                        ih L2 (Z + k + 3) (k + 1) hc'
                          { state := m', pre := preRev.reverse, cur := cq.1,
                            post := (s', false) :: x.post }
                          (fun k' hk' => hb k' (by simp [hk'])) r0 hp0
                      refine ⟨⟨roundCostLeft (q := q) Z k preRev.reverse cq s' + r1'.steps,
                        r1'.z, r1'.c, r1'.hc, r1'.reg⟩, r2, ?_, ?_, ?_, ?_⟩
                      · rw [passRun_left_unfold q b tab Z c hc x k ks hb1 m' s' cq preRev
                          hrev hpick]
                        rw [h1]
                        simp only [Option.map_some]
                      · exact h2
                      · dsimp only at hst ⊢
                        omega
                      · rw [hrg]

/-- **末块无关性（区域层面）**：前缀块列表固定、只把最后一块的值由 `a` 换成 `a'`，
    通路仍成功且终态区域完全相同（末块的值只决定终态计数器与其后继选择）。
    Last-block irrelevance: with the prefix blocks fixed, changing the value of the final
    block leaves success and the final region unchanged. -/
theorem passRun_last_block_irrel (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    ∀ (L : List Nat) (a a' : Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q)
      (hb : ∀ k' ∈ L ++ [a], k' + 2 < 2 ^ b)
      (hb' : ∀ k' ∈ L ++ [a'], k' + 2 < 2 ^ b)
      (r : PassRes q b), passRun q b tab Z c hc x (L ++ [a]) hb = some r →
      ∃ r', passRun q b tab Z c hc x (L ++ [a']) hb' = some r' ∧ r'.reg = r.reg := by
  intro L
  induction L with
  | nil =>
      -- 单块：两条通路做同一轮，只有终态计数器不同
      intro a a' Z c hc x hb hb' r hpass
      simp only [List.nil_append] at hpass ⊢
      have hca' : a' + 2 < 2 ^ b := hb' a' (by simp)
      cases hpk : pick (tab x.state x.cur) c with
      | none =>
          rw [passRun_none_unfold q b tab Z c hc x a [] hb hpk] at hpass
          cases hpass
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [passRun_stay_unfold q b tab Z c hc x a [] hb m' s' hpk] at hpass
              have hrr : r.reg = { state := m', pre := x.pre, cur := s', post := x.post } := by
                simp only [passRun, Option.map_some, Option.some.injEq] at hpass
                rw [← hpass]
              refine ⟨⟨roundCostStay x Z a' s', Z + a' + 3, a' + 1, by omega,
                { state := m', pre := x.pre, cur := s', post := x.post }⟩, ?_, ?_⟩
              · rw [passRun_stay_unfold q b tab Z c hc x a' [] hb' m' s' hpk]
                simp [passRun, Nat.add_zero]
              · rw [hrr]
          | right =>
              cases hpost : x.post with
              | nil =>
                  simp only [passRun, hpk, hpost] at hpass
                  cases hpass
              | cons p post' =>
                  rw [passRun_right_unfold q b tab Z c hc x a [] hb m' s' p post'
                    hpost hpk] at hpass
                  have hrr : r.reg
                      = { state := m', pre := x.pre ++ [(s', false)], cur := p.1,
                          post := post' } := by
                    simp only [passRun, Option.map_some, Option.some.injEq] at hpass
                    rw [← hpass]
                  refine ⟨⟨roundCostRight x Z a' p s', Z + a' + 3, a' + 1, by omega,
                    { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }⟩,
                    ?_, ?_⟩
                  · rw [passRun_right_unfold q b tab Z c hc x a' [] hb' m' s' p post'
                      hpost hpk]
                    simp [passRun, Nat.add_zero]
                  · rw [hrr]
          | left =>
              cases hrev : x.pre.reverse with
              | nil =>
                  simp only [passRun, hpk, hrev] at hpass
                  cases hpass
              | cons cq preRev =>
                  rw [passRun_left_unfold q b tab Z c hc x a [] hb m' s' cq preRev
                    hrev hpk] at hpass
                  have hrr : r.reg
                      = { state := m', pre := preRev.reverse, cur := cq.1,
                          post := (s', false) :: x.post } := by
                    simp only [passRun, Option.map_some, Option.some.injEq] at hpass
                    rw [← hpass]
                  refine ⟨⟨roundCostLeft (q := q) Z a' preRev.reverse cq s', Z + a' + 3,
                    a' + 1, by omega,
                    { state := m', pre := preRev.reverse, cur := cq.1,
                      post := (s', false) :: x.post }⟩, ?_, ?_⟩
                  · rw [passRun_left_unfold q b tab Z c hc x a' [] hb' m' s' cq preRev
                      hrev hpk]
                    simp [passRun, Nat.add_zero]
                  · rw [hrr]
  | cons k0 L' ih =>
      -- 多块：剥掉首轮，对剩余块列表用归纳假设
      intro a a' Z c hc x hb hb' r hpass
      simp only [List.cons_append] at hpass ⊢
      have hkb : k0 + 2 < 2 ^ b := hb k0 (by simp)
      have hc' : k0 + 1 < 2 ^ b := by omega
      cases hpk : pick (tab x.state x.cur) c with
      | none =>
          rw [passRun_none_unfold q b tab Z c hc x k0 (L' ++ [a]) hb hpk] at hpass
          cases hpass
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [passRun_stay_unfold q b tab Z c hc x k0 (L' ++ [a]) hb m' s' hpk] at hpass
              obtain ⟨r0, hrec, hr⟩ := Option.map_eq_some_iff.mp hpass
              obtain ⟨r0', hrec', hreg0⟩ :=
                ih a a' (Z + k0 + 3) (k0 + 1) hc'
                  { state := m', pre := x.pre, cur := s', post := x.post }
                  (fun k' hk' => hb k' (by simp [hk']))
                  (fun k' hk' => hb' k' (by simp [hk'])) r0 hrec
              refine ⟨⟨roundCostStay x Z k0 s' + r0'.steps, r0'.z, r0'.c, r0'.hc,
                r0'.reg⟩, ?_, ?_⟩
              · rw [passRun_stay_unfold q b tab Z c hc x k0 (L' ++ [a']) hb' m' s' hpk]
                rw [hrec']
                simp only [Option.map_some]
              · have hrr : r.reg = r0.reg := (congrArg PassRes.reg hr).symm
                rw [hrr]
                exact hreg0
          | right =>
              cases hpost : x.post with
              | nil =>
                  simp only [passRun, hpk, hpost] at hpass
                  cases hpass
              | cons p post' =>
                  rw [passRun_right_unfold q b tab Z c hc x k0 (L' ++ [a]) hb m' s' p post'
                    hpost hpk] at hpass
                  obtain ⟨r0, hrec, hr⟩ := Option.map_eq_some_iff.mp hpass
                  obtain ⟨r0', hrec', hreg0⟩ :=
                    ih a a' (Z + k0 + 3) (k0 + 1) hc'
                      { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                      (fun k' hk' => hb k' (by simp [hk']))
                      (fun k' hk' => hb' k' (by simp [hk'])) r0 hrec
                  refine ⟨⟨roundCostRight x Z k0 p s' + r0'.steps, r0'.z, r0'.c, r0'.hc,
                    r0'.reg⟩, ?_, ?_⟩
                  · rw [passRun_right_unfold q b tab Z c hc x k0 (L' ++ [a']) hb' m' s' p
                      post' hpost hpk]
                    rw [hrec']
                    simp only [Option.map_some]
                  · have hrr : r.reg = r0.reg := (congrArg PassRes.reg hr).symm
                    rw [hrr]
                    exact hreg0
          | left =>
              cases hrev : x.pre.reverse with
              | nil =>
                  simp only [passRun, hpk, hrev] at hpass
                  cases hpass
              | cons cq preRev =>
                  rw [passRun_left_unfold q b tab Z c hc x k0 (L' ++ [a]) hb m' s' cq preRev
                    hrev hpk] at hpass
                  obtain ⟨r0, hrec, hr⟩ := Option.map_eq_some_iff.mp hpass
                  obtain ⟨r0', hrec', hreg0⟩ :=
                    ih a a' (Z + k0 + 3) (k0 + 1) hc'
                      { state := m', pre := preRev.reverse, cur := cq.1,
                        post := (s', false) :: x.post }
                      (fun k' hk' => hb k' (by simp [hk']))
                      (fun k' hk' => hb' k' (by simp [hk'])) r0 hrec
                  refine ⟨⟨roundCostLeft (q := q) Z k0 preRev.reverse cq s' + r0'.steps,
                    r0'.z, r0'.c, r0'.hc, r0'.reg⟩, ?_, ?_⟩
                  · rw [passRun_left_unfold q b tab Z c hc x k0 (L' ++ [a']) hb' m' s' cq
                      preRev hrev hpk]
                    rw [hrec']
                    simp only [Option.map_some]
                  · have hrr : r.reg = r0.reg := (congrArg PassRes.reg hr).symm
                    rw [hrr]
                    exact hreg0

/-- 通路成功时首轮查表不能失败。
    A successful pass cannot start with a failed lookup. -/
theorem exists_pick_of_passRun_cons (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (k : Nat) (ks : List Nat)
    (hb : ∀ k' ∈ k :: ks, k' + 2 < 2 ^ b) (r : PassRes q b)
    (h : passRun q b tab Z c hc x (k :: ks) hb = some r) :
    ∃ v, pick (tab x.state x.cur) c = some v := by
  cases hp : pick (tab x.state x.cur) c with
  | none =>
      rw [passRun_none_unfold q b tab Z c hc x k ks hb hp] at h
      cases h
  | some v => exact ⟨v, rfl⟩

/-- **前缀区域永不停在接受态**：通路成功且续段非空时，任一真前缀的终态区域
    必不是接受态（否则 `haltNorm` 下续段查表必然失败）。
    No proper prefix of a successful pass ends in the accepting state. -/
theorem passRun_prefix_reg_ne_accept (q b : Nat) (M : NTM q)
    (L1 : List Nat) (k : Nat) (ks : List Nat) (Z c : Nat) (hc : c < 2 ^ b)
    (x : Reg q) (hb : ∀ k' ∈ L1 ++ (k :: ks), k' + 2 < 2 ^ b) (r : PassRes q b)
    (hpass : passRun q b (M.haltNorm).step Z c hc x (L1 ++ (k :: ks)) hb = some r) :
    ∃ r1 : PassRes q b,
      passRun q b (M.haltNorm).step Z c hc x L1
          (fun k' hk' => hb k' (List.mem_append_left (k :: ks) hk')) = some r1 ∧
      r1.reg.state ≠ M.accept := by
  obtain ⟨r1, r2, h1, h2, -, -⟩ :=
    passRun_append q b (M.haltNorm).step L1 (k :: ks) Z c hc x hb r hpass
  refine ⟨r1, h1, ?_⟩
  intro hacc
  have hnone : pick ((M.haltNorm).step r1.reg.state r1.reg.cur) r1.c = none :=
    pick_haltNorm_none M r1.reg r1.c (Or.inl hacc)
  obtain ⟨v, hpv⟩ := exists_pick_of_passRun_cons q b (M.haltNorm).step r1.z r1.c r1.hc
    r1.reg k ks _ r2 h2
  rw [hnone] at hpv
  cases hpv

end DTM

end Pnp
