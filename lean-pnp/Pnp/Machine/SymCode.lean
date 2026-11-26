/-
  文件：Pnp/Machine/SymCode.lean
  主题：纸带符号的非空白编码（布局组件的基础）。

  单带模拟器需要空白 `none` 作为「区域分隔符」。但被模拟纸带的符号本身
  就可能是 `none`，所以数据区不能直接写原始符号，必须先编码成不含空白的位串：

    none        ↦ 00
    some false  ↦ 01
    some true   ↦ 11

  编码只使用 `some false` / `some true`，因此空白可以作为可靠的分隔符。
  本文件给出编码、解码及其往返与「全非空白」性质。
-/

import Pnp.Tape

namespace Pnp

/-- 把纸带符号编码成两个非空白符号。 -/
def symCode : Sym → List Sym
  | none => [some false, some false]
  | some false => [some false, some true]
  | some true => [some true, some true]

/-- 从编码后的前缀解码纸带符号。 -/
def symDecode : List Sym → Option Sym
  | some false :: some false :: _ => some none
  | some false :: some true :: _ => some (some false)
  | some true :: some true :: _ => some (some true)
  | _ => none

/-- 编码后先解码还原原符号。 -/
theorem symDecode_symCode (s : Sym) : symDecode (symCode s) = some s := by
  cases s with
  | none => rfl
  | some b => cases b <;> rfl

/-- 编码结果长度为 2。 -/
theorem symCode_length (s : Sym) : (symCode s).length = 2 := by
  cases s with
  | none => rfl
  | some b => cases b <;> rfl

/-- 编码结果不含空白。 -/
theorem symCode_ne_none (s : Sym) : ∀ x ∈ symCode s, x ≠ none := by
  cases s with
  | none => simp [symCode]
  | some b => cases b <;> simp [symCode]

/-- 编码一个符号列表：拼接各符号的编码。 -/
def codeList (xs : List Sym) : List Sym := xs.flatMap symCode

/-- 编码后的列表不含空白。 -/
theorem codeList_ne_none (xs : List Sym) : ∀ x ∈ codeList xs, x ≠ none := by
  intro x hx
  simp only [codeList, List.mem_flatMap] at hx
  obtain ⟨s, _, hs⟩ := hx
  exact symCode_ne_none s x hs

/-- 编码后列表的长度恰为原长度的两倍。 -/
theorem codeList_length (xs : List Sym) : (codeList xs).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons s rest ih =>
      have ih' : (List.flatMap symCode rest).length = 2 * rest.length := ih
      simp only [codeList, List.flatMap_cons, List.length_append, symCode_length,
        List.length_cons, ih']
      omega

end Pnp
