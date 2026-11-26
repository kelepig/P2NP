/-
  文件：Pnp/Machine/DigitShape.lean
  File: Pnp/Machine/DigitShape.lean

  主题：数字区 `digitArea` 的**规范形状**——各块编码 `0 1^(k+2)` 的拼接，末尾一个空白。
  Topic: canonical shape of the digit area. `digitArea ks` is the concatenation of the
  block codes `0 1^(k+2)`, followed by one boundary blank.

  用途（B5 外层枚举 E）：E 的循环体把数字区当成「低位在左的 B 进制计数器」逐轮改写，
  需要块编码的长度、非空白性（扫尾机器能靠空白识别区尾）与整区长度记账。
  Purpose (E): the loop body rewrites the digit area as a base-`B` counter, so it needs block
  lengths, non-blankness of coded cells, and the total length of the area.
-/

import Pnp.Machine.SimPass

namespace Pnp

namespace DTM

/-- 单块编码：`0 1^(k+2)`。Block code for the value `k`. -/
def blockCode (k : Nat) : List Sym :=
  some false :: List.replicate (k + 2) (some true)

/-- 块编码非空。 -/
theorem blockCode_ne_nil (k : Nat) : blockCode k ≠ [] := by
  simp [blockCode]

/-- 块编码长度：`k + 3`。 -/
theorem blockCode_length (k : Nat) : (blockCode k).length = k + 3 := by
  simp [blockCode]

/-- 块编码的每一格都非空白。 -/
theorem blockCode_ne_none (k : Nat) : ∀ v ∈ blockCode k, v ≠ none := by
  intro v hv
  simp only [blockCode, List.mem_cons, List.mem_replicate] at hv
  rcases hv with rfl | ⟨_, rfl⟩ <;> simp

/-- **数字区的规范形状**：`digitArea ks = 各块编码拼接 ++ [none]`。
    Canonical shape: the digit area is the flattened block codes plus one blank. -/
theorem digitArea_eq_flatMap (ks : List Nat) :
    digitArea ks = (ks.map blockCode).flatten ++ [none] := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      show some false :: (some true :: (List.replicate (k + 1) (some true) ++ digitArea ks))
        = (blockCode k :: ks.map blockCode).flatten ++ [none]
      rw [ih, List.flatten_cons]
      rw [show blockCode k = some false :: (some true :: List.replicate (k + 1) (some true)) from by
        simp [blockCode, show k + 2 = (k + 1) + 1 from by omega, List.replicate_succ]]
      simp only [List.cons_append, List.append_assoc]

/-- **整区长度**：`|digitArea ks| = Σ (k + 3) + 1`。
    Total length of the digit area. -/
theorem digitArea_length (ks : List Nat) :
    (digitArea ks).length = (ks.map (fun k => k + 3)).sum + 1 := by
  induction ks with
  | nil => rfl
  | cons k ks ih =>
      show (some false :: (some true :: (List.replicate (k + 1) (some true)
          ++ digitArea ks))).length = ((k :: ks).map (fun k => k + 3)).sum + 1
      simp only [List.length_cons, List.length_append, List.length_replicate,
        List.map_cons, List.sum_cons, ih]
      omega

/-- **区尾之前全是非空白格**：扫描机器可以靠末尾空白识别数字区终点。
    Everything before the trailing blank is non-blank, so a scanner can find the end. -/
theorem digitArea_init_ne_none (ks : List Nat) :
    ∀ v ∈ (digitArea ks).dropLast, v ≠ none := by
  rw [digitArea_eq_flatMap]
  -- 末尾是 `[none]`，去掉后恰是块编码的拼接
  have hd : ((ks.map blockCode).flatten ++ [none]).dropLast = (ks.map blockCode).flatten :=
    List.dropLast_concat
  rw [hd]
  intro v hv
  obtain ⟨b, hb, hvb⟩ := List.mem_flatten.mp hv
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hb
  exact blockCode_ne_none k v hvb

end DTM

end Pnp
