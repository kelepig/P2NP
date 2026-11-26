/-
  文件：Pnp/Machine/SimPassComplete.lean
  主题：接受方向的语义完备性收口——把「带步数计数、停在接受态的区域迭代」
        转成「存在一条成功通路，其终态区域为接受态」。

  链路（承接 auto-run-log #117 的 5 义务之语义部分）：
    `stepNs M t τ x = some z`（`z` 接受，且 `τ` 的每项都取自一个「全 ≥1 且有界」的
    选择列表 `csS`）
      --exists_stepCs_accept_of_stepNs-->  `stepCs (haltNorm.step) τ' x = some z`（`τ' ⊆ τ`）
      --exists_passRun_of_stepCs_map-->   `passRun … (τ' 尾项减 1 补哑元) = some r` 且 `r.reg = z`。
    之所以要求「全 ≥1」：通路数字区语义是「块值 k ⇒ 下一轮选择 k+1」，故除首项外的选择
    必须 ≥ 1；外层枚举用占位机 `M.stutter` 保证这一点（每个真实选择的索引都 +1）。

  Accept-direction semantic completeness: a counted accepting iteration over choices drawn
  from an all-≥1 bounded list yields a successful pass ending in the accepting state.
-/

import Pnp.Machine.SimStepCs
import Pnp.Machine.SimPassRev

namespace Pnp

namespace DTM

/-- **接受方向完备性**：若带计数的区域迭代 `stepNs M t τ x` 停在接受态 `z`，且 `τ` 的每项
    都取自选择列表 `csS`（其每项满足 `1 ≤ ·` 与 `· + 1 < 2 ^ b`），则存在数字列表 `L`、
    首轮选择 `c` 与成功通路 `r`，通路终态区域正是接受态 `z`。
    Accept-direction completeness: an accepting counted iteration over choices drawn from an
    all-≥1 bounded list admits a successful pass ending in the accepting state. -/
theorem exists_passRun_accept_of_stepNs_bounded {q b : Nat} (M : NTM q)
    (Z : Nat) (x : Reg q) (csS : List Nat)
    (hAll : ∀ a ∈ csS, 1 ≤ a ∧ a + 1 < 2 ^ b)
    (hb2 : 2 < 2 ^ b)
    (t : Nat) (τ : List Nat) (z : Reg q)
    (hmem : ∀ a ∈ τ, a ∈ csS)
    (hstepNs : stepNs M t τ x = some z) (hacc : z.state = M.accept) :
    ∃ (L : List Nat) (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) (c : Nat) (hc : c < 2 ^ b)
      (r : PassRes q b),
      passRun q b (M.haltNorm).step Z c hc x L hb = some r ∧ r.reg.state = M.accept := by
  -- 第一步：把计数迭代转成无计数折叠（取实际消耗的前缀 τ'）
  obtain ⟨τ', _hlen, hmem', hfold⟩ :=
    exists_stepCs_accept_of_stepNs M t τ x z hstepNs hacc
  have hAllτ' : ∀ a ∈ τ', 1 ≤ a ∧ a + 1 < 2 ^ b :=
    fun a ha => hAll a (hmem a (hmem' a ha))
  cases τ' with
  | nil =>
      -- 零步即接受：折叠原地返回 `x`，故 `z = x`，取空数字列表
      simp only [stepCs, Option.some.injEq] at hfold
      subst hfold
      refine ⟨[], by simp, 0, Nat.two_pow_pos b, ⟨0, Z, 0, Nat.two_pow_pos b, x⟩, ?_, ?_⟩
      · rfl
      · exact hacc
  | cons a' rest' =>
      -- 首项若非空：把 `a'` 作为首轮选择，其余减 1 补哑元成为数字列表
      have hfirst : 1 ≤ a' ∧ a' + 1 < 2 ^ b := hAllτ' a' List.mem_cons_self
      obtain ⟨r, hpass, hreg⟩ :=
        exists_passRun_of_stepCs_map q b (M.haltNorm).step a' (by omega) 0 hb2 rest'
          (fun y hy => (hAllτ' y (List.mem_cons_of_mem a' hy)).1)
          (fun y hy => (hAllτ' y (List.mem_cons_of_mem a' hy)).2) Z x z hfold
      refine ⟨rest'.map (fun y => y - 1) ++ [0], ?_, a', by omega, r, ?_, ?_⟩
      · -- 数字列表各项加 2 仍 < 2^b（由 `csS` 的上界传递）
        intro k' hk'
        rcases List.mem_append.mp hk' with hm | hs
        · obtain ⟨d, hdmem, rfl⟩ := List.mem_map.mp hm
          have hd := hAllτ' d (List.mem_cons_of_mem a' hdmem)
          have h3 : d - 1 + 2 = d + 1 := by omega
          omega
        · simp only [List.mem_singleton] at hs
          subst hs
          omega
      · exact hpass
      · rw [hreg]
        exact hacc

/-- **带长度界的接受完备性**：同 `exists_passRun_accept_of_stepNs_bounded`，额外保证
    数字列表 `L` 的长度不超过原选择列表 `τ` 的长度（`L` 取自实际消耗的前缀）。
    Accept completeness with the extra length bound `|L| ≤ |τ|`. -/
theorem exists_passRun_accept_of_stepNs_bounded_len {q b : Nat} (M : NTM q)
    (Z : Nat) (x : Reg q) (csS : List Nat)
    (hAll : ∀ a ∈ csS, 1 ≤ a ∧ a + 1 < 2 ^ b)
    (hb2 : 2 < 2 ^ b)
    (t : Nat) (τ : List Nat) (z : Reg q)
    (hmem : ∀ a ∈ τ, a ∈ csS)
    (hstepNs : stepNs M t τ x = some z) (hacc : z.state = M.accept) :
    ∃ (L : List Nat) (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) (c : Nat) (hc : c < 2 ^ b)
      (r : PassRes q b),
      passRun q b (M.haltNorm).step Z c hc x L hb = some r ∧ r.reg.state = M.accept ∧
        L.length ≤ τ.length := by
  obtain ⟨τ', hlen, hmem', hfold⟩ :=
    exists_stepCs_accept_of_stepNs M t τ x z hstepNs hacc
  have hAllτ' : ∀ a ∈ τ', 1 ≤ a ∧ a + 1 < 2 ^ b :=
    fun a ha => hAll a (hmem a (hmem' a ha))
  cases τ' with
  | nil =>
      simp only [stepCs, Option.some.injEq] at hfold
      subst hfold
      refine ⟨[], by simp, 0, Nat.two_pow_pos b, ⟨0, Z, 0, Nat.two_pow_pos b, x⟩, rfl, hacc, ?_⟩
      simp
  | cons a' rest' =>
      have hfirst : 1 ≤ a' ∧ a' + 1 < 2 ^ b := hAllτ' a' List.mem_cons_self
      obtain ⟨r, hpass, hreg⟩ :=
        exists_passRun_of_stepCs_map q b (M.haltNorm).step a' (by omega) 0 hb2 rest'
          (fun y hy => (hAllτ' y (List.mem_cons_of_mem a' hy)).1)
          (fun y hy => (hAllτ' y (List.mem_cons_of_mem a' hy)).2) Z x z hfold
      have hlen' : rest'.length + 1 ≤ τ.length := by
        have := hlen
        rw [List.length_cons] at this
        exact this
      refine ⟨rest'.map (fun y => y - 1) ++ [0], ?_, a', by omega, r, hpass, ?_, ?_⟩
      · intro k' hk'
        rcases List.mem_append.mp hk' with hm | hs
        · obtain ⟨d, hdmem, rfl⟩ := List.mem_map.mp hm
          have hd := hAllτ' d (List.mem_cons_of_mem a' hdmem)
          have h3 : d - 1 + 2 = d + 1 := by omega
          omega
        · simp only [List.mem_singleton] at hs
          subst hs
          omega
      · rw [hreg]
        exact hacc
      · rw [List.length_append, List.length_map, List.length_singleton]
        exact hlen'

end DTM

end Pnp
