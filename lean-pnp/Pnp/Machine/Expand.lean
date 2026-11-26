/-
  文件：Pnp/Machine/Expand.lean
  File: Pnp/Machine/Expand.lean

  主题：**区域右侧原始符号块的就地展开机**——把非空白符号串 `l` 逐格改写成
        格编码 `[codeFst a, codeSnd a, some false]`，每写一格就把剩余块整体右移两格。
  Topic: in-place expansion of a raw (all non-blank) block into 3-symbol cell codes;
  each round shifts the remaining block two cells to the right.

  为什么只能「自左向右 + 状态携带两个符号」：2-格右移需 `new[j] = old[j-2]`，
  自右向左要预读左方两格（尚不知道），故不可行（设计见 docs/07 末节）。
  Why left-to-right with a two-symbol carry: `new[j] = old[j-2]` needs old data
  already read, which only holds when moving right.

  状态布局：0 入口；`qLoop xi yi s ci`（`xi,yi` 为两个携带符号的情形、`s` 是否已启动、
  `ci = 情形-1`），转移写成按 `st.val` 的字面量 `match`，便于 `rfl` 归约；
  `50+2ph+ci` 回扫/落码；`60+2ph+ci` 末符号直接写下；99 接受。
-/

import Pnp.Machine.PadLeft

namespace Pnp

namespace DTM

/-- 循环状态编码：`xi,yi` 为携带符号情形，`s ∈ {0,1}` 表示是否已启动，`ci = 情形-1`。 -/
abbrev qLoop (xi yi s ci : Nat) : Nat := 10 + xi * 12 + yi * 4 + s * 2 + ci

/-- **展开机**（128 状态）：入口 0，回扫段 `50..59`，末符号段 `60..67`，接受 99。 -/
def expand : DTM 128 where
  step := fun st a =>
    match st.val with
    | 0 =>
      (match a with
       | none => (⟨99, by omega⟩, none, Dir.stay)
       | some b =>
         (⟨(match b with | false => 10 | true => 11), by split <;> omega⟩, some b, Dir.right))
    | 10 =>
      (match a with
       | none => (⟨60, by omega⟩, codeSnd (some false), Dir.left)
       | some b => (⟨10 + 0 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, none, Dir.right))
    | 11 =>
      (match a with
       | none => (⟨61, by omega⟩, codeSnd (some true), Dir.left)
       | some b => (⟨10 + 0 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, none, Dir.right))
    | 12 =>
      (match a with
       | none => (⟨50, by omega⟩, a, Dir.left)
       | some b => (⟨10 + 0 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, none, Dir.right))
    | 13 =>
      (match a with
       | none => (⟨51, by omega⟩, a, Dir.left)
       | some b => (⟨10 + 0 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, none, Dir.right))
    | 14 =>
      (match a with
       | none => (⟨10 + 12 + 2 + 0, by omega⟩, none, Dir.right)
       | some b => (⟨10 + 12 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, none, Dir.right))
    | 15 =>
      (match a with
       | none => (⟨10 + 12 + 2 + 1, by omega⟩, none, Dir.right)
       | some b => (⟨10 + 12 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, none, Dir.right))
    | 16 =>
      (match a with
       | none => (⟨10 + 12 + 2 + 0, by omega⟩, none, Dir.right)
       | some b => (⟨10 + 12 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, none, Dir.right))
    | 17 =>
      (match a with
       | none => (⟨10 + 12 + 2 + 1, by omega⟩, none, Dir.right)
       | some b => (⟨10 + 12 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, none, Dir.right))
    | 18 =>
      (match a with
       | none => (⟨10 + 24 + 2 + 0, by omega⟩, none, Dir.right)
       | some b => (⟨10 + 24 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, none, Dir.right))
    | 19 =>
      (match a with
       | none => (⟨10 + 24 + 2 + 1, by omega⟩, none, Dir.right)
       | some b => (⟨10 + 24 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, none, Dir.right))
    | 20 =>
      (match a with
       | none => (⟨10 + 24 + 2 + 0, by omega⟩, none, Dir.right)
       | some b => (⟨10 + 24 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, none, Dir.right))
    | 21 =>
      (match a with
       | none => (⟨10 + 24 + 2 + 1, by omega⟩, none, Dir.right)
       | some b => (⟨10 + 24 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, none, Dir.right))
    | 22 =>
      (match a with
       | none => (⟨10 + 0 + 2 + 0, by omega⟩, some false, Dir.right)
       | some b => (⟨10 + 0 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, some false, Dir.right))
    | 23 =>
      (match a with
       | none => (⟨10 + 0 + 2 + 1, by omega⟩, some false, Dir.right)
       | some b => (⟨10 + 0 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, some false, Dir.right))
    | 24 =>
      (match a with
       | none => (⟨10 + 0 + 2 + 0, by omega⟩, some false, Dir.right)
       | some b => (⟨10 + 0 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, some false, Dir.right))
    | 25 =>
      (match a with
       | none => (⟨10 + 0 + 2 + 1, by omega⟩, some false, Dir.right)
       | some b => (⟨10 + 0 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, some false, Dir.right))
    | 26 =>
      (match a with
       | none => (⟨10 + 12 + 2 + 0, by omega⟩, some false, Dir.right)
       | some b => (⟨10 + 12 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, some false, Dir.right))
    | 27 =>
      (match a with
       | none => (⟨10 + 12 + 2 + 1, by omega⟩, some false, Dir.right)
       | some b => (⟨10 + 12 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, some false, Dir.right))
    | 28 =>
      (match a with
       | none => (⟨10 + 12 + 2 + 0, by omega⟩, some false, Dir.right)
       | some b => (⟨10 + 12 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, some false, Dir.right))
    | 29 =>
      (match a with
       | none => (⟨10 + 12 + 2 + 1, by omega⟩, some false, Dir.right)
       | some b => (⟨10 + 12 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, some false, Dir.right))
    | 30 =>
      (match a with
       | none => (⟨10 + 24 + 2 + 0, by omega⟩, some false, Dir.right)
       | some b => (⟨10 + 24 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, some false, Dir.right))
    | 31 =>
      (match a with
       | none => (⟨10 + 24 + 2 + 1, by omega⟩, some false, Dir.right)
       | some b => (⟨10 + 24 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, some false, Dir.right))
    | 32 =>
      (match a with
       | none => (⟨10 + 24 + 2 + 0, by omega⟩, some false, Dir.right)
       | some b => (⟨10 + 24 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, some false, Dir.right))
    | 33 =>
      (match a with
       | none => (⟨10 + 24 + 2 + 1, by omega⟩, some false, Dir.right)
       | some b => (⟨10 + 24 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, some false, Dir.right))
    | 34 =>
      (match a with
       | none => (⟨10 + 0 + 2 + 0, by omega⟩, some true, Dir.right)
       | some b => (⟨10 + 0 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, some true, Dir.right))
    | 35 =>
      (match a with
       | none => (⟨10 + 0 + 2 + 1, by omega⟩, some true, Dir.right)
       | some b => (⟨10 + 0 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, some true, Dir.right))
    | 36 =>
      (match a with
       | none => (⟨10 + 0 + 2 + 0, by omega⟩, some true, Dir.right)
       | some b => (⟨10 + 0 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, some true, Dir.right))
    | 37 =>
      (match a with
       | none => (⟨10 + 0 + 2 + 1, by omega⟩, some true, Dir.right)
       | some b => (⟨10 + 0 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, some true, Dir.right))
    | 38 =>
      (match a with
       | none => (⟨10 + 12 + 2 + 0, by omega⟩, some true, Dir.right)
       | some b => (⟨10 + 12 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, some true, Dir.right))
    | 39 =>
      (match a with
       | none => (⟨10 + 12 + 2 + 1, by omega⟩, some true, Dir.right)
       | some b => (⟨10 + 12 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, some true, Dir.right))
    | 40 =>
      (match a with
       | none => (⟨10 + 12 + 2 + 0, by omega⟩, some true, Dir.right)
       | some b => (⟨10 + 12 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, some true, Dir.right))
    | 41 =>
      (match a with
       | none => (⟨10 + 12 + 2 + 1, by omega⟩, some true, Dir.right)
       | some b => (⟨10 + 12 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, some true, Dir.right))
    | 42 =>
      (match a with
       | none => (⟨10 + 24 + 2 + 0, by omega⟩, some true, Dir.right)
       | some b => (⟨10 + 24 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, some true, Dir.right))
    | 43 =>
      (match a with
       | none => (⟨10 + 24 + 2 + 1, by omega⟩, some true, Dir.right)
       | some b => (⟨10 + 24 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, some true, Dir.right))
    | 44 =>
      (match a with
       | none => (⟨10 + 24 + 2 + 0, by omega⟩, some true, Dir.right)
       | some b => (⟨10 + 24 + (match b with | false => 1 | true => 2) * 4 + 2 + 0, by split <;> omega⟩, some true, Dir.right))
    | 45 =>
      (match a with
       | none => (⟨10 + 24 + 2 + 1, by omega⟩, some true, Dir.right)
       | some b => (⟨10 + 24 + (match b with | false => 1 | true => 2) * 4 + 2 + 1, by split <;> omega⟩, some true, Dir.right))
    | 50 =>
      (match a with
       | none => (⟨52, by omega⟩, some false, Dir.left)
       | some b => (⟨50, by omega⟩, some b, Dir.left))
    | 51 =>
      (match a with
       | none => (⟨53, by omega⟩, some false, Dir.left)
       | some b => (⟨51, by omega⟩, some b, Dir.left))
    | 52 =>
      (⟨54, by omega⟩, codeSnd (some false), Dir.left)
    | 53 =>
      (⟨55, by omega⟩, codeSnd (some true), Dir.left)
    | 54 =>
      (⟨56, by omega⟩, codeFst (some false), Dir.right)
    | 55 =>
      (⟨57, by omega⟩, codeFst (some true), Dir.right)
    | 56 =>
      (⟨58, by omega⟩, a, Dir.right)
    | 57 =>
      (⟨59, by omega⟩, a, Dir.right)
    | 58 =>
      (⟨0, by omega⟩, a, Dir.right)
    | 59 =>
      (⟨0, by omega⟩, a, Dir.right)
    | 60 =>
      (⟨62, by omega⟩, codeFst (some false), Dir.right)
    | 61 =>
      (⟨63, by omega⟩, codeFst (some true), Dir.right)
    | 62 =>
      (⟨64, by omega⟩, a, Dir.right)
    | 63 =>
      (⟨65, by omega⟩, a, Dir.right)
    | 64 =>
      (⟨0, by omega⟩, some false, Dir.right)
    | 65 =>
      (⟨0, by omega⟩, some false, Dir.right)
    | _ => (st, a, Dir.stay)
  start := ⟨0, by omega⟩
  accept := ⟨99, by omega⟩
  reject := ⟨99, by omega⟩

/-- 非 99 状态一律不停机。 -/
theorem expand_halted_ne (st : Nat) (hst : st < 128) (h : st ≠ 99) (t : Tape) :
    expand.halted ⟨⟨st, hst⟩, t⟩ = false := by
  simp only [DTM.halted, expand]
  rw [Bool.or_self, beq_eq_false_iff_ne]
  intro hh
  exact h (congrArg Fin.val hh)

end DTM

end Pnp
