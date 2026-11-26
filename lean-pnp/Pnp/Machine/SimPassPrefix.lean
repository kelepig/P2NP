/-
  文件：Pnp/Machine/SimPassPrefix.lean
  主题：通路的**前缀分解**——跑满前 `|L1|` 轮后，驱动层恰好落在「前缀 `passRun`
        结果」所描述的区域，数字区剩余后缀 `L2`。

  为什么需要它（docs/decisions/auto-run-log.md #93）：外层枚举要证明
  「观察机命中接受哨兵 ⇒ 存在使 NTM 接受的选择前缀」。观察机在轮起点看到的
  `m` 就是该轮起点的区域状态；把时刻按轮分解后，这一状态正是前缀 `passRun`
  的终态区域，于是可用 `passRun_reg` + `runWith_of_stepCs` 收口。

  Prefix decomposition of a successful pass: after the first |L1| rounds the drive
  sits exactly at the region described by `passRun` on the prefix, with suffix digits.
-/

import Pnp.Machine.SimPass
import Pnp.Machine.SimVerdict

namespace Pnp

namespace DTM

/-- **通路前缀分解**：对任意前缀分解 `L = L1 ++ L2`，若前缀通路 `passRun` 成功，
    则驱动层跑满前缀的步数后，状态正对应前缀结果 `r1`，数字区剩余 `L2`。
    Prefix decomposition: running the first |L1| rounds lands on the prefix result. -/
theorem simDrive_pass_prefix (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q) :
    ∀ (L1 : List Nat) (L2 : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q)
      (m : Nat) (hm : m < q),
      x.state = (⟨m, hm⟩ : Fin q) →
      (∀ p0 ∈ x.pre, p0.2 = false) →
      (∀ p0 ∈ x.post, p0.2 = false) →
      (hb : ∀ k' ∈ L1, k' + 2 < 2 ^ b) →
      ∀ (r1 : PassRes q b),
        passRun q b tab Z c hc x L1 hb = some r1 →
        (simDrive q b tab s0).run r1.steps
            (passStart x m c hm hc Z (L1 ++ L2)) =
          passStart r1.reg r1.reg.state.val r1.c r1.reg.state.isLt r1.hc r1.z L2 := by
  intro L1
  induction L1 with
  | nil =>
      intro L2 Z c hc x m hm hx hpre hpost hb r1 hpass
      simp only [passRun, Option.some.injEq] at hpass
      cases hpass
      simp only [List.nil_append, DTM.run]
      refine (Config.mk.injEq _ _ _ _).mpr ⟨?_, ?_⟩
      · apply Fin.ext
        simp only [passStart, Config.state, embS, Fin.val_mk, codeState_val]
        have hv : m = x.state.val := (congrArg Fin.val hx).symm
        rw [hv]
      · simp only [passStart, Config.tape]
  | cons k L1' ih =>
      intro L2 Z c hc x m hm hx hpre hpost hb r1 hpass
      -- 把 `(k :: L1') ++ L2` 规范成 `k :: (L1' ++ L2)`，便于与单轮引理匹配
      simp only [List.cons_append] at hpass ⊢
      obtain ⟨xc, X', htail⟩ := digitArea_split (L1' ++ L2)
      have hxc := digitArea_head_ne_true (L1' ++ L2) xc X' htail
      have hkb : k + 2 < 2 ^ b := hb k (by rw [List.mem_cons]; exact Or.inl rfl)
      have hb' : ∀ k' ∈ L1', k' + 2 < 2 ^ b :=
        fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')
      cases hpk : pick (tab x.state x.cur) c with
      | none =>
          rw [passRun_none_unfold q b tab Z c hc x k L1' hb hpk] at hpass
          cases hpass
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [passRun_stay_unfold q b tab Z c hc x k L1' hb m' s' hpk] at hpass
              cases hrec : passRun q b tab (Z + k + 3) (k + 1)
                  (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                  { state := m', pre := x.pre, cur := s', post := x.post } L1' hb' with
              | none => rw [hrec] at hpass; cases hpass
              | some r0 =>
                  rw [hrec] at hpass
                  simp only [Option.map_some, Option.some.injEq] at hpass
                  cases hpass
                  have hcan := simDrive_roundCanon_stay q b tab s0 m c hm hc x Z k (k + 2)
                    hkb rfl xc X' hxc hpre m' s' hx hpk (L1' ++ L2) htail
                  rw [DTM.run_add, hcan]
                  have hx' : ({ state := m', pre := x.pre, cur := s', post := x.post } : Reg q).state
                      = (⟨m'.val, m'.isLt⟩ : Fin q) := by cases m'; rfl
                  exact ih L2 (Z + k + 3) (k + 1)
                    (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                    { state := m', pre := x.pre, cur := s', post := x.post } m'.val m'.isLt
                    hx' hpre hpost hb' r0 hrec
          | right =>
              cases hpost0 : x.post with
              | nil =>
                  rw [passRun_right_nil_unfold q b tab Z c hc x k L1' hb m' s' hpost0 hpk]
                    at hpass
                  cases hpass
              | cons p post' =>
                  rw [passRun_right_unfold q b tab Z c hc x k L1' hb m' s' p post' hpost0 hpk]
                    at hpass
                  cases hrec : passRun q b tab (Z + k + 3) (k + 1)
                      (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                      { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                      L1' hb' with
                  | none => rw [hrec] at hpass; cases hpass
                  | some r0 =>
                      rw [hrec] at hpass
                      simp only [Option.map_some, Option.some.injEq] at hpass
                      cases hpass
                      have hp : p.2 = false := hpost p (by rw [hpost0]; simp)
                      have hpre' : ∀ p0 ∈ x.pre ++ [(s', false)], p0.2 = false := by
                        intro p0 hp0
                        rcases List.mem_append.mp hp0 with hp0' | hp0'
                        · exact hpre p0 hp0'
                        · rw [List.mem_singleton] at hp0'
                          subst hp0'
                          rfl
                      have hpost' : ∀ p0 ∈ post', p0.2 = false :=
                        fun p0 hp0 => hpost p0 (by rw [hpost0]; exact List.mem_cons_of_mem _ hp0)
                      have hcan := simDrive_roundCanon_right q b tab s0 m c hm hc x Z k (k + 2)
                        hkb rfl xc X' hxc hpre p post' hp hpost0 m' s' hx hpk (L1' ++ L2) htail
                      rw [DTM.run_add, hcan]
                      have hx' : (Reg.mk m' (x.pre ++ [(s', false)]) p.1 post' : Reg q).state
                          = (⟨m'.val, m'.isLt⟩ : Fin q) := by cases m'; rfl
                      exact ih L2 (Z + k + 3) (k + 1)
                        (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                        { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                        m'.val m'.isLt hx' hpre' hpost' hb' r0 hrec
          | left =>
              cases hrev : x.pre.reverse with
              | nil =>
                  rw [passRun_left_nil_unfold q b tab Z c hc x k L1' hb m' s' hrev hpk] at hpass
                  cases hpass
              | cons cq preRev =>
                  rw [passRun_left_unfold q b tab Z c hc x k L1' hb m' s' cq preRev hrev hpk]
                    at hpass
                  cases hrec : passRun q b tab (Z + k + 3) (k + 1)
                      (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                      (Reg.mk m' preRev.reverse cq.1 ((s', false) :: x.post)) L1' hb' with
                  | none => rw [hrec] at hpass; cases hpass
                  | some r0 =>
                      rw [hrec] at hpass
                      simp only [Option.map_some, Option.some.injEq] at hpass
                      cases hpass
                      have hpre2 : x.pre = preRev.reverse ++ [cq] := by
                        rw [← List.reverse_reverse x.pre, hrev, List.reverse_cons]
                      have hq : cq.2 = false :=
                        hpre cq (by rw [hpre2]; exact List.mem_append_right _ (by simp))
                      have hpre' : ∀ p0 ∈ preRev.reverse, p0.2 = false := by
                        intro p0 hp0
                        exact hpre p0 (by rw [hpre2]; exact List.mem_append_left _ hp0)
                      have hpost' : ∀ p0 ∈ (s', false) :: x.post, p0.2 = false := by
                        intro p0 hp0
                        rcases List.mem_cons.mp hp0 with hp0' | hp0'
                        · subst hp0'
                          rfl
                        · exact hpost p0 hp0'
                      have hcan := simDrive_roundCanon_left q b tab s0 m c hm hc x Z k (k + 2)
                        hkb rfl xc X' hxc hpre cq preRev.reverse hq hpre2 m' s' hx hpk
                        (L1' ++ L2) htail
                      rw [DTM.run_add, hcan]
                      have hx' : (Reg.mk m' preRev.reverse cq.1 ((s', false) :: x.post) : Reg q).state
                          = (⟨m'.val, m'.isLt⟩ : Fin q) := by cases m'; rfl
                      exact ih L2 (Z + k + 3) (k + 1)
                        (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                        (Reg.mk m' preRev.reverse cq.1 ((s', false) :: x.post))
                        m'.val m'.isLt hx' hpre' hpost' hb' r0 hrec

/-- **前缀成功**：整条通路成功时，任意前缀通路也成功。
    Prefix success: a successful pass restricts to successful prefixes. -/
theorem passRun_prefix_some (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    ∀ (L1 L2 : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q)
      (hb : ∀ k' ∈ L1 ++ L2, k' + 2 < 2 ^ b) (r : PassRes q b),
      passRun q b tab Z c hc x (L1 ++ L2) hb = some r →
      ∃ r1 : PassRes q b,
        passRun q b tab Z c hc x L1 (fun k' hk' => hb k' (List.mem_append_left L2 hk'))
          = some r1 := by
  intro L1
  induction L1 with
  | nil =>
      intro L2 Z c hc x hb r hpass
      exact ⟨⟨0, Z, c, hc, x⟩, by simp only [passRun]⟩
  | cons k L1' ih =>
      intro L2 Z c hc x hb r hpass
      -- `(k :: L1') ++ L2` 规范成 `k :: (L1' ++ L2)`（假设与目标一起规范）
      simp only [List.cons_append] at hb hpass
      have hkb : k + 2 < 2 ^ b := hb k List.mem_cons_self
      have hbT : ∀ k' ∈ L1' ++ L2, k' + 2 < 2 ^ b :=
        fun k' hk' => hb k' (List.mem_cons_of_mem k hk')
      have hb' : ∀ k' ∈ L1', k' + 2 < 2 ^ b :=
        fun k' hk' => hbT k' (List.mem_append_left L2 hk')
      have hb0 : ∀ k' ∈ k :: L1', k' + 2 < 2 ^ b := by
        intro k' hk'
        rcases List.mem_cons.mp hk' with rfl | hk''
        · exact hkb
        · exact hb' k' hk''
      cases hpk : pick (tab x.state x.cur) c with
      | none =>
          rw [passRun_none_unfold q b tab Z c hc x k (L1' ++ L2) hb hpk] at hpass
          cases hpass
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [passRun_stay_unfold q b tab Z c hc x k (L1' ++ L2) hb m' s' hpk] at hpass
              obtain ⟨r0, hr0⟩ : ∃ r0, passRun q b tab (Z + k + 3) (k + 1)
                  (by have := hb k List.mem_cons_self; omega)
                  { state := m', pre := x.pre, cur := s', post := x.post } (L1' ++ L2) hbT
                  = some r0 := by
                cases hrc : passRun q b tab (Z + k + 3) (k + 1)
                    (by have := hb k List.mem_cons_self; omega)
                    { state := m', pre := x.pre, cur := s', post := x.post } (L1' ++ L2) hbT
                  with
                | none => rw [hrc] at hpass; cases hpass
                | some r0 => exact ⟨r0, rfl⟩
              obtain ⟨r1', hr1'⟩ := ih L2 (Z + k + 3) (k + 1)
                (by have := hb k List.mem_cons_self; omega)
                { state := m', pre := x.pre, cur := s', post := x.post } hbT r0 hr0
              exact ⟨_, by
                rw [passRun_stay_unfold q b tab Z c hc x k L1' hb0 m' s' hpk, hr1']
                rfl⟩
          | right =>
              cases hpost0 : x.post with
              | nil =>
                  rw [passRun_right_nil_unfold q b tab Z c hc x k (L1' ++ L2) hb m' s'
                    hpost0 hpk] at hpass
                  cases hpass
              | cons p post' =>
                  rw [passRun_right_unfold q b tab Z c hc x k (L1' ++ L2) hb m' s' p post'
                    hpost0 hpk] at hpass
                  obtain ⟨r0, hr0⟩ : ∃ r0, passRun q b tab (Z + k + 3) (k + 1)
                      (by have := hb k List.mem_cons_self; omega)
                      { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                      (L1' ++ L2) hbT = some r0 := by
                    cases hrc : passRun q b tab (Z + k + 3) (k + 1)
                        (by have := hb k List.mem_cons_self; omega)
                        { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                        (L1' ++ L2) hbT with
                    | none => rw [hrc] at hpass; cases hpass
                    | some r0 => exact ⟨r0, rfl⟩
                  obtain ⟨r1', hr1'⟩ := ih L2 (Z + k + 3) (k + 1)
                    (by have := hb k List.mem_cons_self; omega)
                    { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                    hbT r0 hr0
                  exact ⟨_, by
                    rw [passRun_right_unfold q b tab Z c hc x k L1' hb0 m' s' p post' hpost0 hpk,
                      hr1']
                    rfl⟩
          | left =>
              cases hrev : x.pre.reverse with
              | nil =>
                  rw [passRun_left_nil_unfold q b tab Z c hc x k (L1' ++ L2) hb m' s'
                    hrev hpk] at hpass
                  cases hpass
              | cons cq preRev =>
                  rw [passRun_left_unfold q b tab Z c hc x k (L1' ++ L2) hb m' s' cq preRev
                    hrev hpk] at hpass
                  obtain ⟨r0, hr0⟩ : ∃ r0, passRun q b tab (Z + k + 3) (k + 1)
                      (by have := hb k List.mem_cons_self; omega)
                      (Reg.mk m' preRev.reverse cq.1 ((s', false) :: x.post))
                      (L1' ++ L2) hbT = some r0 := by
                    cases hrc : passRun q b tab (Z + k + 3) (k + 1)
                        (by have := hb k List.mem_cons_self; omega)
                        (Reg.mk m' preRev.reverse cq.1 ((s', false) :: x.post))
                        (L1' ++ L2) hbT with
                    | none => rw [hrc] at hpass; cases hpass
                    | some r0 => exact ⟨r0, rfl⟩
                  obtain ⟨r1', hr1'⟩ := ih L2 (Z + k + 3) (k + 1)
                    (by have := hb k List.mem_cons_self; omega)
                    (Reg.mk m' preRev.reverse cq.1 ((s', false) :: x.post)) hbT r0 hr0
                  exact ⟨_, by
                    rw [passRun_left_unfold q b tab Z c hc x k L1' hb0 m' s' cq preRev hrev hpk,
                      hr1']
                    rfl⟩

end DTM

end Pnp
