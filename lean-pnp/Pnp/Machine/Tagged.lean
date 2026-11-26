/-
  文件：Pnp/Machine/Tagged.lean
  主题：「数字标签」组合器 `tagged`：把一台机器 A 的状态空间放大 `B` 倍，
        让状态携带一个数字标签 `d < B`（布局：`d * q + p`）。

  用途：B5 的搜索驱动需要「读到的选择编号 d」在后续阶段（找标记、模拟一轮）
  一直留在状态里。`tagged` 不改 A 的纸带行为，只把状态改成 `d * q + p`。

  本文件给出：
    - `tagged A B`：放大后的机器（状态数 `B*q + 1`，最后一个状态未使用）；
    - `taggedEmb`：标签 `d` 与状态 `p` 的嵌入；
    - `tagged_step` / `tagged_halted_false` / `tagged_run`（用 `run_embed`）。

  注意：与 `run_embed` 一样，整段运行要求 A 在这些步内不停机。
-/

import Pnp.Machine.Embed
import Pnp.Machine.TaggedBase
import Pnp.Machine.SeekNoHalt

namespace Pnp

namespace DTM

/-- 把机器 A 的状态空间放大 `B` 倍：状态 `d*q+p` 表示「标签 `d` + A 状态 `p`」。 -/
def tagged {q : Nat} (A : DTM q) (B : Nat) : DTM (B * q + 1) where
  step := fun st a =>
    if h : st.val < B * q then
      if hq : q = 0 then (st, a, Dir.stay)
      else
        let d := st.val / q
        let p := st.val % q
        let r := A.step ⟨p, Nat.mod_lt _ (Nat.pos_of_ne_zero hq)⟩ a
        (⟨d * q + r.1.val, by
            have hd : d < B :=
              Nat.div_lt_of_lt_mul (by rwa [Nat.mul_comm q B] : st.val < q * B)
            have hdq : d * q + q ≤ B * q :=
              calc d * q + q = (d + 1) * q := by rw [Nat.add_mul, Nat.one_mul]
                _ ≤ B * q := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hd)
            have hp : r.1.val < q := r.1.isLt
            omega⟩, r.2.1, r.2.2)
    else (st, a, Dir.stay)
  start := ⟨0, by omega⟩
  accept := ⟨B * q, by omega⟩
  reject := ⟨B * q, by omega⟩

/-- 标签 `d` 与状态 `p` 的嵌入。 -/
def taggedEmb {q : Nat} (B : Nat) (d : Nat) (hdB : d < B) (hq : 0 < q) :
    Fin q → Fin (B * q + 1) :=
  fun p => ⟨d * q + p.val, by
    have hdq : d * q + q ≤ B * q :=
      calc d * q + q = (d + 1) * q := by rw [Nat.add_mul, Nat.one_mul]
        _ ≤ B * q := Nat.mul_le_mul_right q (Nat.succ_le_of_lt hdB)
    have hp : p.val < q := p.isLt
    omega⟩

/-- 嵌入状态上的单步：`tagged A B` 照抄 A 的转移，标签不变。 -/
theorem tagged_step {q : Nat} (A : DTM q) (B d : Nat) (hdB : d < B) (hq : 0 < q)
    (p : Fin q) (a : Sym) :
    (tagged A B).step (taggedEmb B d hdB hq p) a =
      (taggedEmb B d hdB hq (A.step p a).1, (A.step p a).2.1, (A.step p a).2.2) := by
  have hlt : (taggedEmb B d hdB hq p).val < B * q := by
    have h0 := add_mul_lt_mul hdB p.isLt
    simpa [taggedEmb] using h0
  have hval_eq : (taggedEmb B d hdB hq p).val = d * q + p.val := rfl
  have hdiv : (taggedEmb B d hdB hq p).val / q = d := by
    rw [hval_eq, Nat.mul_comm d q, Nat.mul_add_div hq]
    simp only [Nat.div_eq_of_lt p.isLt, Nat.add_zero]
  have hmod : (taggedEmb B d hdB hq p).val % q = p.val := by
    rw [hval_eq, Nat.add_comm, Nat.add_mul_mod_self_right]
    exact Nat.mod_eq_of_lt p.isLt
  simp only [tagged]
  rw [dif_pos hlt, dif_neg (by omega : ¬ q = 0)]
  simp only [hdiv, hmod]
  rfl

/-- 嵌入状态在 `tagged A B` 中未停机。 -/
theorem tagged_halted_false {q : Nat} (A : DTM q) (B d : Nat) (hdB : d < B) (hq : 0 < q)
    (p : Fin q) (t : Tape) :
    (tagged A B).halted (Config.mk (taggedEmb B d hdB hq p) t) = false := by
  have hval : (taggedEmb B d hdB hq p).val < B * q := by
    have h0 := add_mul_lt_mul hdB p.isLt
    simpa [taggedEmb] using h0
  have hneA : (taggedEmb B d hdB hq p) ≠ (⟨B * q, by omega⟩ : Fin (B * q + 1)) := by
    intro hh
    have hv : (taggedEmb B d hdB hq p).val = B * q := by
      have := congrArg Fin.val hh
      simpa only [Fin.val_mk] using this
    omega
  unfold DTM.halted tagged
  rw [beq_eq_false_iff_ne.mpr hneA]
  rfl

/-- 把 A 的 `n` 步运行搬进 `tagged A B`（标签 `d` 不变）。 -/
theorem tagged_run {q : Nat} (A : DTM q) (B d : Nat) (hdB : d < B) (hq : 0 < q)
    (n : Nat) (c : Config q) (hA : ∀ m, m < n → A.halted (A.run m c) = false) :
    (tagged A B).run n
        { state := taggedEmb B d hdB hq c.state, tape := c.tape } =
      { state := taggedEmb B d hdB hq (A.run n c).state, tape := (A.run n c).tape } := by
  refine run_embed A (tagged A B) (taggedEmb B d hdB hq) ?_ ?_ n c hA
  · intro s a _ _
    exact tagged_step A B d hdB hq s a
  · intro s _ _
    have hval : (taggedEmb B d hdB hq s).val < B * q := by
      have h0 := add_mul_lt_mul hdB s.isLt
      simpa [taggedEmb] using h0
    have hne : (taggedEmb B d hdB hq s) ≠ (⟨B * q, by omega⟩ : Fin (B * q + 1)) := by
      intro hh
      have hv : (taggedEmb B d hdB hq s).val = B * q := by
        have := congrArg Fin.val hh
        simpa only [Fin.val_mk] using this
      omega
    exact ⟨fun heq => hne heq.symm, fun heq => hne heq.symm⟩

/-- 带数字标签的找标记运行（接口版）：若能保证入参 `seekMark` 在段内不停机，
    `tagged seekMark B` 的整段运行与 `seekMark` 一致、标签 `d` 不变。 -/
theorem seekMark_tagged_run {B d : Nat} (hdB : d < B) (hq : 0 < 4)
    (cs : List (Sym × Bool)) (h : ∀ p ∈ cs, p.2 = false)
    (s : Sym) (rest : List (Sym × Bool)) (L : List Sym)
    (hnh : ∀ m, m < 3 * cs.length + 3 →
      seekMark.halted (seekMark.run m
        { state := (0 : Fin 4),
          tape := { left := L, right := codeCells cs ++ cellCode (s, true) ++ codeCells rest } })
        = false) :
    (tagged seekMark B).run (3 * cs.length + 3)
        { state := taggedEmb B d hdB hq (0 : Fin 4),
          tape := { left := L, right := codeCells cs ++ cellCode (s, true) ++ codeCells rest } } =
      { state := taggedEmb B d hdB hq (3 : Fin 4),
        tape := { left := List.reverse (codeCells cs ++ symCode s) ++ L,
                  right := some true :: codeCells rest } } := by
  rw [tagged_run seekMark B d hdB hq (3 * cs.length + 3)
    { state := (0 : Fin 4),
      tape := { left := L, right := codeCells cs ++ cellCode (s, true) ++ codeCells rest } } hnh]
  rw [seekMark_run cs h s rest L]

/-- 带数字标签的找标记运行（无额外假设版）：`hnh` 由 `seekMark_halted_false_before` 给出。 -/
theorem seekMark_tagged_run' {B d : Nat} (hdB : d < B) (hq : 0 < 4)
    (cs : List (Sym × Bool)) (h : ∀ p ∈ cs, p.2 = false)
    (s : Sym) (rest : List (Sym × Bool)) (L : List Sym) :
    (tagged seekMark B).run (3 * cs.length + 3)
        { state := taggedEmb B d hdB hq (0 : Fin 4),
          tape := { left := L, right := codeCells cs ++ cellCode (s, true) ++ codeCells rest } } =
      { state := taggedEmb B d hdB hq (3 : Fin 4),
        tape := { left := List.reverse (codeCells cs ++ symCode s) ++ L,
                  right := some true :: codeCells rest } } := by
  exact seekMark_tagged_run hdB hq cs h s rest L
    (fun m hm => seekMark_halted_false_before cs h s rest L m hm)

end DTM

end Pnp
