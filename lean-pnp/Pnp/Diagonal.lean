/-
  文件：Pnp/Diagonal.lean
  主题：对角线论证（diagonal argument）的机器核验版本。

  为什么先写它：
    P vs NP 的每一次下界尝试，底层几乎都是某种对角线或计数论证。
    康托定理是最纯粹的形式：任何「把每个元素映射到一组元素」的规则，
    都不可能覆盖所有组。罗素悖论、哥德尔不完备、图灵停机不可判定，
    都是同一结构的变体。

  本文件不依赖 Mathlib，只用 Lean 4 内核，构建在秒级完成。
-/

namespace Pnp

/--
  康托对角线定理（函数版）。

  设 `f : α → (α → Prop)` 是把每个元素 `a` 映射到一个「集合」（用谓词表示）的规则。
  结论：不存在这样的 `f`，使得每个谓词 `p` 都有某个 `a` 满足 `f a = p`。

  证明思路（对角线）：
    假设存在满射 `f`。定义对角线集合
      `d x := ¬ f x x`
    即「x 不属于它自己所对应的集合」。
    由满射性，存在 `a` 使 `f a = d`。
    把 `a` 代入：`f a a ↔ ¬ f a a`，两边互为否定，矛盾。
-/
theorem cantor_no_surjection (α : Type) (f : α → α → Prop) :
    ¬ ∀ p : α → Prop, ∃ a : α, f a = p := by
  -- 反证：假设 f 是满射
  intro hf
  -- 构造对角线谓词 d：d x 成立当且仅当 x 不属于 f x
  let d : α → Prop := fun x => ¬ f x x
  -- 由满射性取原像 a，满足 f a = d
  rcases hf d with ⟨a, ha⟩
  -- 关键一步：把 a 代入，得到「f a a 当且仅当非 f a a」
  -- 注意：不能用 rw 整体重写，否则会同时改到 ¬ f a a 内部的 f a a；
  -- 这里先得到命题之间的一条等式，再按需要方向转换。
  have hEq : f a a = (¬ f a a) := (congrFun ha a).trans rfl
  have h : f a a ↔ ¬ f a a :=
    ⟨fun hp => hEq ▸ hp, fun hn => hEq.symm ▸ hn⟩
  -- 一个命题与它的否定等价，必然矛盾：
  -- 若 f a a 成立，则 h 给出其否定并立即自相矛盾；
  -- 把该否定再喂给 h，又推出 f a a 成立，再次矛盾。
  exact (fun hp => (h.mp hp) hp) (h.mpr (fun hp => (h.mp hp) hp))

end Pnp
