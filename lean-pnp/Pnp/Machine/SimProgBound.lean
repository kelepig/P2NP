/-
  文件：Pnp/Machine/SimProgBound.lean
  主题：通路进度线性不变量——零计数 `z` 上界（义务 d 分步前提）。
  `passRun_z_le`：`r.z ≤ Z + |ks|·(2^b+3)`（每轮 `z` 增 `k+3`，块值 `k<2^b`）。
  Linear zero-counter invariant for the pass.
-/
import Pnp.Machine.SimCostBound

namespace Pnp
namespace DTM

/-- `(n+1)*X = n*X + X`。 -/
theorem natMul_succ (n X : Nat) : (n + 1) * X = n * X + X := by
  rw [Nat.add_mul, Nat.one_mul]

/-- 零计数上界：`r.z ≤ Z + |ks|·(2^b+3)`。 -/
theorem passRun_z_le (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    ∀ (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (ks : List Nat)
      (hb : ∀ k' ∈ ks, k' + 2 < 2 ^ b) (r : PassRes q b),
      passRun q b tab Z c hc x ks hb = some r → r.z ≤ Z + ks.length * (2 ^ b + 3) := by
  intro Z c hc x ks
  induction ks generalizing Z c hc x with
  | nil =>
      intro hb r hpass
      simp only [passRun, Option.some.injEq] at hpass
      subst hpass; simp
  | cons k ks ih =>
      intro hb r hpass
      simp only [passRun] at hpass
      have hk : k + 3 ≤ 2 ^ b + 3 := by
        have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega
      cases hpk : pick (tab x.state x.cur) c with
      | none => rw [hpk] at hpass; exact absurd hpass (by simp)
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [hpk, Option.map_eq_some_iff] at hpass
              obtain ⟨r0, hr0, hr0r⟩ := hpass
              have hzr : r.z = r0.z := by rw [← hr0r]
              rw [hzr, List.length_cons, natMul_succ]
              have hz := ih (Z + k + 3) (k + 1)
                (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                { state := m', pre := x.pre, cur := s', post := x.post }
                (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hr0
              omega
          | right =>
              cases hpost : x.post with
              | nil => rw [hpk, hpost] at hpass; exact absurd hpass (by simp)
              | cons p post' =>
                  rw [hpk, hpost, Option.map_eq_some_iff] at hpass
                  obtain ⟨r0, hr0, hr0r⟩ := hpass
                  have hzr : r.z = r0.z := by rw [← hr0r]
                  rw [hzr, List.length_cons, natMul_succ]
                  have hz := ih (Z + k + 3) (k + 1)
                    (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                    { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                    (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hr0
                  omega
          | left =>
              cases hrev : x.pre.reverse with
              | nil => rw [hpk, hrev] at hpass; exact absurd hpass (by simp)
              | cons cq preRev =>
                  rw [hpk, hrev, Option.map_eq_some_iff] at hpass
                  obtain ⟨r0, hr0, hr0r⟩ := hpass
                  have hzr : r.z = r0.z := by rw [← hr0r]
                  rw [hzr, List.length_cons, natMul_succ]
                  have hz := ih (Z + k + 3) (k + 1)
                    (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                    { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post }
                    (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hr0
                  omega

/-- 前缀格数上界：`r.reg.pre.length ≤ |x.pre| + |ks|`。 -/
theorem passRun_pre_le (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    ∀ (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (ks : List Nat)
      (hb : ∀ k' ∈ ks, k' + 2 < 2 ^ b) (r : PassRes q b),
      passRun q b tab Z c hc x ks hb = some r → r.reg.pre.length ≤ x.pre.length + ks.length := by
  intro Z c hc x ks
  induction ks generalizing Z c hc x with
  | nil =>
      intro hb r hp
      simp only [passRun, Option.some.injEq] at hp
      subst hp; simp
  | cons k ks ih =>
      intro hb r hp
      simp only [passRun] at hp
      have ihx : ∀ (Z c : Nat) (hc : c < 2 ^ b) (y : Reg q) (r0 : PassRes q b),
          passRun q b tab Z c hc y ks
            (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) = some r0 →
          r0.reg.pre.length ≤ y.pre.length + ks.length :=
        fun Z c hc y r0 h => ih Z c hc y
          (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 h
      cases hpk : pick (tab x.state x.cur) c with
      | none => rw [hpk] at hp; exact absurd hp (by simp)
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [hpk, Option.map_eq_some_iff] at hp
              obtain ⟨r0, hr0, hr0r⟩ := hp
              have hreg : r.reg = r0.reg := by rw [← hr0r]
              rw [hreg, List.length_cons]
              have h := ihx (Z + k + 3) (k + 1)
                (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                { state := m', pre := x.pre, cur := s', post := x.post } r0 hr0
              dsimp only at h
              omega
          | right =>
              cases hpost : x.post with
              | nil => rw [hpk, hpost] at hp; exact absurd hp (by simp)
              | cons p post' =>
                  rw [hpk, hpost, Option.map_eq_some_iff] at hp
                  obtain ⟨r0, hr0, hr0r⟩ := hp
                  have hreg : r.reg = r0.reg := by rw [← hr0r]
                  rw [hreg, List.length_cons]
                  have h := ihx (Z + k + 3) (k + 1)
                    (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                    { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } r0 hr0
                  rw [List.length_append, List.length_singleton] at h
                  omega
          | left =>
              cases hrev : x.pre.reverse with
              | nil => rw [hpk, hrev] at hp; exact absurd hp (by simp)
              | cons cq preRev =>
                  rw [hpk, hrev, Option.map_eq_some_iff] at hp
                  obtain ⟨r0, hr0, hr0r⟩ := hp
                  have hreg : r.reg = r0.reg := by rw [← hr0r]
                  rw [hreg, List.length_cons]
                  have h := ihx (Z + k + 3) (k + 1)
                    (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                    { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } r0 hr0
                  rw [List.length_reverse] at h
                  have hlen : preRev.length + 1 = x.pre.length := by
                    have := congrArg List.length hrev
                    rw [List.length_reverse, List.length_cons] at this; omega
                  omega

/-- 单轮成本上限函数：`40 + 6(P+T) + 2(Z + T(Bk+3)) + 2Bk`。 -/
def costCap (P Z T Bk : Nat) : Nat := 40 + 6 * (P + T) + 2 * (Z + T * (Bk + 3)) + 2 * Bk

/-- `costCap` 单步单调：前缀至多 +1、`Z` 至多 +Bk+3、轮数减 1 后，上限不增。
    One-step monotonicity of the cap. -/
theorem costCap_mono (P Z T P' Z' T' Bk : Nat)
    (hP : P' ≤ P + 1) (hZ : Z' ≤ Z + Bk + 3) (hT : T' + 1 ≤ T) :
    costCap P' Z' T' Bk ≤ costCap P Z T Bk := by
  unfold costCap
  have h6 : 6 * (P' + T') ≤ 6 * (P + T) := by
    apply Nat.mul_le_mul_left
    omega
  have hZ2 : Z' + T' * (Bk + 3) ≤ Z + T * (Bk + 3) := by
    have hX : (T' + 1) * (Bk + 3) ≤ T * (Bk + 3) := Nat.mul_le_mul_right _ hT
    have hm : (T' + 1) * (Bk + 3) = T' * (Bk + 3) + (Bk + 3) := natMul_succ _ _
    have h1 : T' * (Bk + 3) + (Bk + 3) ≤ T * (Bk + 3) := by rw [← hm]; exact hX
    calc Z' + T' * (Bk + 3) ≤ (Z + Bk + 3) + T' * (Bk + 3) :=
          Nat.add_le_add_right hZ _
      _ = Z + (T' * (Bk + 3) + (Bk + 3)) := by omega
      _ ≤ Z + T * (Bk + 3) := Nat.add_le_add_left h1 _
  have h2 : 2 * (Z' + T' * (Bk + 3)) ≤ 2 * (Z + T * (Bk + 3)) :=
    Nat.mul_le_mul_left 2 hZ2
  omega

/-- **通路总步数上界**：`r.steps ≤ |ks| · costCap(|x.pre|, Z, |ks|, 2^b)`。 -/
theorem passRun_steps_le (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    ∀ (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (ks : List Nat)
      (hb : ∀ k' ∈ ks, k' + 2 < 2 ^ b) (r : PassRes q b),
      passRun q b tab Z c hc x ks hb = some r →
      r.steps ≤ ks.length * costCap x.pre.length Z ks.length (2 ^ b) := by
  intro Z c hc x ks
  induction ks generalizing Z c hc x with
  | nil =>
      intro hb r hp
      simp only [passRun, Option.some.injEq] at hp
      subst hp; simp
  | cons k ks ih =>
      intro hb r hp
      simp only [passRun] at hp
      have hkB : k < 2 ^ b := by
        have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega
      cases hpk : pick (tab x.state x.cur) c with
      | none => rw [hpk] at hp; exact absurd hp (by simp)
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [hpk, Option.map_eq_some_iff] at hp
              obtain ⟨r0, hr0, hr0r⟩ := hp
              have hsteps : r.steps = roundCostStay x Z k s' + r0.steps := by rw [← hr0r]
              have h0 := ih (Z + k + 3) (k + 1)
                (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                { state := m', pre := x.pre, cur := s', post := x.post } (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hr0
              have hmono : ks.length * costCap x.pre.length (Z + k + 3) ks.length (2 ^ b)
                  ≤ ks.length * costCap x.pre.length Z (ks.length + 1) (2 ^ b) :=
                Nat.mul_le_mul_left ks.length
                  (costCap_mono _ _ _ _ _ _ _ (by omega) (by omega) (by omega))
              have hcost : roundCostStay x Z k s'
                  ≤ costCap x.pre.length Z (ks.length + 1) (2 ^ b) := by
                unfold costCap; rw [Nat.mul_add, Nat.mul_add]
                have := roundCostStay_le x Z k s'; omega
              rw [hsteps, List.length_cons, natMul_succ]
              exact Nat.le_trans (Nat.add_le_add hcost (Nat.le_trans h0 hmono))
                (Nat.le_of_eq (Nat.add_comm _ _))
          | right =>
              cases hpost : x.post with
              | nil => rw [hpk, hpost] at hp; exact absurd hp (by simp)
              | cons p post' =>
                  rw [hpk, hpost, Option.map_eq_some_iff] at hp
                  obtain ⟨r0, hr0, hr0r⟩ := hp
                  have hsteps : r.steps = roundCostRight x Z k p s' + r0.steps := by rw [← hr0r]
                  have hlen : (x.pre ++ [(s', false)]).length = x.pre.length + 1 := by
                    rw [List.length_append, List.length_singleton]
                  have h0 := ih (Z + k + 3) (k + 1)
                    (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                    { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hr0
                  rw [hlen] at h0
                  have hmono : ks.length * costCap (x.pre.length + 1) (Z + k + 3) ks.length (2 ^ b)
                      ≤ ks.length * costCap x.pre.length Z (ks.length + 1) (2 ^ b) :=
                    Nat.mul_le_mul_left ks.length
                      (costCap_mono _ _ _ _ _ _ _ (by omega) (by omega) (by omega))
                  have hcost : roundCostRight x Z k p s'
                      ≤ costCap x.pre.length Z (ks.length + 1) (2 ^ b) := by
                    unfold costCap; rw [Nat.mul_add, Nat.mul_add]
                    have := roundCostRight_le x Z k p s'; omega
                  rw [hsteps, List.length_cons, natMul_succ]
                  exact Nat.le_trans (Nat.add_le_add hcost (Nat.le_trans h0 hmono))
                    (Nat.le_of_eq (Nat.add_comm _ _))
          | left =>
              cases hrev : x.pre.reverse with
              | nil => rw [hpk, hrev] at hp; exact absurd hp (by simp)
              | cons cq preRev =>
                  rw [hpk, hrev, Option.map_eq_some_iff] at hp
                  obtain ⟨r0, hr0, hr0r⟩ := hp
                  have hsteps : r.steps = roundCostLeft (q := q) Z k preRev.reverse cq s' + r0.steps := by rw [← hr0r]
                  have hlen : preRev.length + 1 = x.pre.length := by
                    have := congrArg List.length hrev
                    rw [List.length_reverse, List.length_cons] at this; omega
                  have h0 := ih (Z + k + 3) (k + 1)
                    (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                    { state := m', pre := preRev.reverse, cur := cq.1, post := (s', false) :: x.post } (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hr0
                  rw [List.length_reverse] at h0
                  have hmono : ks.length * costCap preRev.length (Z + k + 3) ks.length (2 ^ b)
                      ≤ ks.length * costCap x.pre.length Z (ks.length + 1) (2 ^ b) :=
                    Nat.mul_le_mul_left ks.length
                      (costCap_mono _ _ _ _ _ _ _ (by omega) (by omega) (by omega))
                  have hcost : roundCostLeft (q := q) Z k preRev.reverse cq s'
                      ≤ costCap x.pre.length Z (ks.length + 1) (2 ^ b) := by
                    unfold costCap; rw [Nat.mul_add, Nat.mul_add]
                    have h := roundCostLeft_le (q := q) Z k preRev.reverse cq s'
                    rw [List.length_reverse] at h; omega
                  rw [hsteps, List.length_cons, natMul_succ]
                  exact Nat.le_trans (Nat.add_le_add hcost (Nat.le_trans h0 hmono))
                    (Nat.le_of_eq (Nat.add_comm _ _))

end DTM
end Pnp
