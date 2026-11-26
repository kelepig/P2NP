/-
  文件：Pnp/Pigeonhole.lean
  主题：有限鸽笼原理（pigeonhole principle）的核心库版本。

  命题：不存在从 Fin (n+1) 到 Fin n 的单射。
  意义：这是「计数型下界」的最小样板。对角化给出「不可能覆盖」，
        鸽笼给出「必有碰撞」，两者共同构成复杂性下界证明的底层工具。

  证明策略：
    对 n 归纳。设 f : Fin (n+2) → Fin (n+1) 是单射，
    令 b = f (最后一个元素)，把值域 Fin (n+1) 中删掉 b 后压成 Fin n，
    得到新的单射 g : Fin (n+1) → Fin n，与归纳假设矛盾。
-/

namespace Pnp

/-- 删掉值 `b` 后，把 `Fin (n+1)` 的元素压回 `Fin n`：
    小于 b 的原样保留，否则减一。要求 v ≠ b，避免把 b 也压进结果。 -/
def eraseVal (n : Nat) (b : Fin (n + 1)) (v : Fin (n + 1))
    (hv : v ≠ b) : Fin n :=
  if h : v.val < b.val then
    -- 小于 b：原样保留。分支条件 h 与上界一起交给 omega
    ⟨v.val, by
      have hblt : b.val < n + 1 := b.isLt
      omega⟩
  else
    -- 不小于 b：减一。v ≠ b 保证 v > b，从而 v - 1 不越过上界
    ⟨v.val - 1, by
      have hvlt : v.val < n + 1 := v.isLt
      have hblt : b.val < n + 1 := b.isLt
      have hne : v.val ≠ b.val := fun hh => hv (Fin.ext hh)
      omega⟩

/-- `eraseVal` 在去掉 b 之后是单射。 -/
theorem eraseVal_inj (n : Nat) (b : Fin (n + 1)) {v w : Fin (n + 1)}
    (hv : v ≠ b) (hw : w ≠ b)
    (h : eraseVal n b v hv = eraseVal n b w hw) : v = w := by
  -- 由 v ≠ b 得到值不相等，供 omega 使用
  have hv' : v.val ≠ b.val := fun hh => hv (Fin.ext hh)
  have hw' : w.val ≠ b.val := fun hh => hw (Fin.ext hh)
  unfold eraseVal at h
  -- 按 v、w 与 b 的大小关系分四种情况；分支条件显式命名，供 omega 使用
  by_cases hvb : v.val < b.val
  · by_cases hwb : w.val < b.val
    · -- 两者都小于 b：值相等即原值相等
      simp only [dite_eq_left hvb, dite_eq_left hwb] at h
      exact Fin.ext (by simpa using congrArg Fin.val h)
    · -- v < b ≤ w：会推出 w.val = b.val，与 w ≠ b 矛盾
      simp only [dite_eq_left hvb, dite_eq_right hwb] at h
      have hval : v.val = w.val - 1 := by simpa using congrArg Fin.val h
      omega
  · by_cases hwb : w.val < b.val
    · -- w < b ≤ v：与上一种情况对称
      simp only [dite_eq_right hvb, dite_eq_left hwb] at h
      have hval : v.val - 1 = w.val := by simpa using congrArg Fin.val h
      omega
    · -- 两者都不小于 b：都减一，原值相等
      simp only [dite_eq_right hvb, dite_eq_right hwb] at h
      have hval : v.val - 1 = w.val - 1 := by simpa using congrArg Fin.val h
      omega

/-- 有限鸽笼原理：不存在从 n+1 个元素到 n 个元素的单射。 -/
theorem fin_no_injective (n : Nat) :
    ¬ ∃ f : Fin (n + 1) → Fin n, Function.Injective f := by
  induction n with
  | zero =>
      -- Fin 1 → Fin 0：值域为空，任何函数都无法取值
      rintro ⟨f, _⟩
      exact Fin.elim0 (f 0)
  | succ n ih =>
      rintro ⟨f, hf⟩
      -- b 是值域中「被最后那个元素占住」的值
      let b : Fin (n + 1) := f (Fin.last (n + 1))
      -- 关键：f 在 castSucc 的像上永远不等于 b，否则与单射性冲突
      have hne : ∀ i : Fin (n + 1), f (Fin.castSucc i) ≠ b := by
        intro i hEq
        have hlast : Fin.castSucc i = Fin.last (n + 1) := hf hEq
        have hv := congrArg Fin.val hlast
        simp [Fin.castSucc, Fin.last] at hv
        omega
      -- 把前 n+1 个输入映射过去，再删掉 b，得到 Fin (n+1) → Fin n
      let g : Fin (n + 1) → Fin n := fun i =>
        eraseVal n b (f (Fin.castSucc i)) (hne i)
      -- g 是单射：eraseVal 单射 + f 单射
      have hg : Function.Injective g := by
        intro i j hij
        have h1 : f (Fin.castSucc i) = f (Fin.castSucc j) :=
          eraseVal_inj n b (hne i) (hne j) hij
        have h2 : Fin.castSucc i = Fin.castSucc j := hf h1
        exact Fin.ext (by simpa [Fin.castSucc] using congrArg Fin.val h2)
      -- 与归纳假设矛盾
      exact ih ⟨g, hg⟩

end Pnp
