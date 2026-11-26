/-
  文件：Pnp/Machine/PackIndex.lean
  主题：把多个有限计数器压成一个自然数（单带模拟器的状态编码）。

  单带模拟器的一步需要同时记住：

    - 被模拟状态 m（范围 < q）；
    - 本次选择编号 c（范围 < 基数 D，实际取 D = 2^b）；
    - 符号编号与移动方向的组合 z（范围 < 9）；
    - 阶段 phase（范围 < P，P 是固定的小常数）。

  图灵机的状态只能是 `Fin N`，所以要把四元组压成一个自然数：

      packIdx D Z P m c z ph = (((m * D + c) * Z + z) * P + ph)

  本文件给出解包函数与往返引理，以及解包结果的取值范围引理。
  这些是后续「查表机」构造 `Fin N` 状态时所需的全部算术。
-/

import Pnp.Classes

namespace Pnp

namespace DTM

/-- 把 `(m, c, z, ph)` 压成一个自然数。 -/
def packIdx (D Z P m c z ph : Nat) : Nat :=
  ((m * D + c) * Z + z) * P + ph

/-- 解出 m。 -/
def unpackM (D Z P n : Nat) : Nat := n / (D * Z * P)

/-- 解出 c。 -/
def unpackC (D Z P n : Nat) : Nat := (n / (Z * P)) % D

/-- 解出 z。 -/
def unpackZ (D Z P n : Nat) : Nat := (n / P) % Z

/-- 解出阶段。 -/
def unpackPh (_D _Z P n : Nat) : Nat := n % P

/-- 阶段解包：`(X * P + ph) % P = ph % P`。 -/
theorem unpackPh_pack (D Z P m c z ph : Nat) :
    unpackPh D Z P (packIdx D Z P m c z ph) = ph % P := by
  unfold unpackPh packIdx
  rw [Nat.add_comm (((m * D + c) * Z + z) * P) ph,
    Nat.add_mul_mod_self_right]

/-- `ph < P` 时阶段解包就是原值。 -/
theorem unpackPh_pack_of_lt (D Z P m c z ph : Nat) (hph : ph < P) :
    unpackPh D Z P (packIdx D Z P m c z ph) = ph := by
  rw [unpackPh_pack, Nat.mod_eq_of_lt hph]

/-- z 解包：先整除掉 `P`，再对 `Z` 取模。 -/
theorem unpackZ_pack (D Z P m c z ph : Nat) (hP : 0 < P) (hph : ph < P) :
    unpackZ D Z P (packIdx D Z P m c z ph) = z % Z := by
  unfold unpackZ packIdx
  rw [Nat.mul_comm (((m * D + c) * Z + z)) P, Nat.mul_add_div hP,
    Nat.div_eq_of_lt hph, Nat.add_zero,
    Nat.add_comm (((m * D + c) * Z)) z, Nat.add_mul_mod_self_right]

/-- `z < Z` 时 z 解包就是原值。 -/
theorem unpackZ_pack_of_lt (D Z P m c z ph : Nat) (hZ : 0 < Z) (hP : 0 < P)
    (hph : ph < P) (hz : z < Z) :
    unpackZ D Z P (packIdx D Z P m c z ph) = z := by
  rw [unpackZ_pack D Z P m c z ph hP hph, Nat.mod_eq_of_lt hz]

/-- 高位算式改写成「主干 * (Z*P) + 余项」。 -/
theorem packIdx_split (D Z P m c z ph : Nat) :
    packIdx D Z P m c z ph
      = (m * D + c) * (Z * P) + (z * P + ph) := by
  unfold packIdx
  rw [Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

/-- c 解包：整除掉 `Z*P` 后对 `D` 取模。 -/
theorem unpackC_pack (D Z P m c z ph : Nat) (hZ : 0 < Z) (hP : 0 < P)
    (hz : z < Z) (hph : ph < P) :
    unpackC D Z P (packIdx D Z P m c z ph) = c % D := by
  unfold unpackC
  rw [packIdx_split,
    Nat.mul_comm (m * D + c) (Z * P),
    Nat.mul_add_div (Nat.mul_pos hZ hP)]
  have hrem : (z * P + ph) / (Z * P) = 0 := by
    rw [Nat.div_eq_of_lt]
    calc z * P + ph < z * P + P := Nat.add_lt_add_left hph _
      _ = (z + 1) * P := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ Z * P := Nat.mul_le_mul_right P hz
  rw [hrem, Nat.add_zero, Nat.add_comm (m * D) c, Nat.add_mul_mod_self_right]

/-- `c < D` 时 c 解包就是原值。 -/
theorem unpackC_pack_of_lt (D Z P m c z ph : Nat) (hD : 0 < D) (hZ : 0 < Z)
    (hP : 0 < P) (hz : z < Z) (hph : ph < P) (hc : c < D) :
    unpackC D Z P (packIdx D Z P m c z ph) = c := by
  rw [unpackC_pack D Z P m c z ph hZ hP hz hph, Nat.mod_eq_of_lt hc]

/-- 主干算式改写成「最高位 * (D*Z*P) + 余项」。 -/
theorem packIdx_split2 (D Z P m c z ph : Nat) :
    packIdx D Z P m c z ph
      = m * (D * Z * P) + (c * (Z * P) + (z * P + ph)) := by
  have h1 : packIdx D Z P m c z ph
      = (m * D) * (Z * P) + (c * (Z * P) + (z * P + ph)) := by
    rw [packIdx_split, Nat.add_mul, Nat.add_assoc]
  rw [h1]
  congr 1
  rw [Nat.mul_assoc, Nat.mul_assoc]

/-- m 解包：整除掉 `D*Z*P`。 -/
theorem unpackM_pack (D Z P m c z ph : Nat) (hD : 0 < D) (hZ : 0 < Z)
    (hP : 0 < P) (hc : c < D) (hz : z < Z) (hph : ph < P) :
    unpackM D Z P (packIdx D Z P m c z ph) = m := by
  unfold unpackM
  rw [packIdx_split2, Nat.mul_comm m (D * Z * P),
    Nat.mul_add_div (Nat.mul_pos (Nat.mul_pos hD hZ) hP)]
  have hzP : z * P + ph < Z * P := by
    calc z * P + ph < z * P + P := Nat.add_lt_add_left hph _
      _ = (z + 1) * P := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ Z * P := Nat.mul_le_mul_right P hz
  have hrem : (c * (Z * P) + (z * P + ph)) / (D * Z * P) = 0 := by
    rw [Nat.div_eq_of_lt]
    calc c * (Z * P) + (z * P + ph)
        < c * (Z * P) + Z * P := Nat.add_lt_add_left hzP _
      _ = (c + 1) * (Z * P) := by rw [Nat.add_mul, Nat.one_mul]
      _ ≤ D * (Z * P) := Nat.mul_le_mul_right _ hc
      _ = D * Z * P := by rw [Nat.mul_assoc]
  rw [hrem, Nat.add_zero]


/-- `m` 在 0..D.. 范围内时 m 解包就是原值。 -/
theorem unpackM_pack_of_lt (D Z P m c z ph : Nat) (hD : 0 < D) (hZ : 0 < Z)
    (hP : 0 < P) (hc : c < D) (hz : z < Z) (hph : ph < P) :
    unpackM D Z P (packIdx D Z P m c z ph) = m :=
  unpackM_pack D Z P m c z ph hD hZ hP hc hz hph

/-- c 解包后总是小于基数。 -/
theorem unpackC_lt (D Z P n : Nat) (hD : 0 < D) : unpackC D Z P n < D := by
  unfold unpackC
  exact Nat.mod_lt _ hD

/-- z 解包后总是小于基数。 -/
theorem unpackZ_lt (D Z P n : Nat) (hZ : 0 < Z) : unpackZ D Z P n < Z := by
  unfold unpackZ
  exact Nat.mod_lt _ hZ

/-- 阶段解包后总是小于阶段数。 -/
theorem unpackPh_lt (D Z P n : Nat) (hP : 0 < P) : unpackPh D Z P n < P := by
  unfold unpackPh
  exact Nat.mod_lt _ hP

end DTM

end Pnp
