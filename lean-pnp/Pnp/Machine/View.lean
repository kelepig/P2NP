/-
  文件：Pnp/Machine/View.lean
  主题：纸带的「整体内容 + 读写头位置」视角。

  直接用 `left` / `right` 两个列表做机器证明时，左右移动会不断把元素
  在两侧搬来搬去，写起来很啰嗦。这里引入：

    - `Tape.view t = t.left.reverse ++ t.right`：整条纸带从左到右的内容；
    - `Tape.headPos t = t.left.length`：读写头在 `view` 中的下标。

  注意：左右移动一般**不改变**内容，只有在纸带端点处才会补出空白；
  本文件把这几种边界情况都证成引理。
-/

import Pnp.Tape

namespace Pnp

namespace Tape

/-- 整条纸带从左到右的内容。 -/
def view (t : Tape) : List Sym := t.left.reverse ++ t.right

/-- 读写头在 `view` 中的下标。 -/
def headPos (t : Tape) : Nat := t.left.length

/-- 初始纸带的内容就是输入（逐符号包成 `some`）。 -/
theorem view_ofInput (w : List Bool) : (ofInput w).view = w.map some := by
  simp [view, ofInput]

/-- 从读写头位置往右看，正好是 `right`。 -/
theorem view_drop_headPos (t : Tape) : t.view.drop t.headPos = t.right := by
  simp [view, headPos]

/-- 当前读到符号等于内容串在头位置处的首符号。 -/
theorem read_eq_view_drop (t : Tape) :
    t.read = (t.view.drop t.headPos).headD none := by
  rw [view_drop_headPos]
  rfl

/-- 右移后头位置加一（端点处也会补出一个新格）。 -/
theorem headPos_moveRight (t : Tape) : t.moveRight.headPos = t.headPos + 1 := by
  cases hr : t.right with
  | nil => simp [headPos, moveRight, hr]
  | cons r rs => simp [headPos, moveRight, hr]

/-- 左移后头位置减一（已是最左端则保持不变）。 -/
theorem headPos_moveLeft (t : Tape) : t.moveLeft.headPos = t.headPos - 1 := by
  cases hl : t.left with
  | nil => simp [headPos, moveLeft, hl]
  | cons l ls => simp [headPos, moveLeft, hl]

/-- 右侧非空时，右移不改变整体内容。 -/
theorem view_moveRight_cons (t : Tape) (r : Sym) (rs : List Sym) (h : t.right = r :: rs) :
    t.moveRight.view = t.view := by
  simp [view, moveRight, h, List.reverse_cons]

/-- 右侧为空时，右移在内容末尾补一个空白。 -/
theorem view_moveRight_nil (t : Tape) (h : t.right = []) :
    t.moveRight.view = t.view ++ [none] := by
  simp [view, moveRight, h, List.reverse_cons]

/-- 左侧非空时，左移不改变整体内容。 -/
theorem view_moveLeft_cons (t : Tape) (l : Sym) (ls : List Sym) (h : t.left = l :: ls) :
    t.moveLeft.view = t.view := by
  simp [view, moveLeft, h, List.reverse_cons, List.append_assoc]

/-- 左侧为空时，左移在内容开头补一个空白。 -/
theorem view_moveLeft_nil (t : Tape) (h : t.left = []) :
    t.moveLeft.view = none :: t.view := by
  simp [view, moveLeft, h]

/-- `drop 1` 就是 `tail`。 -/
theorem drop_one (l : List Sym) : l.drop 1 = l.tail := by
  cases l <;> rfl

end Tape

end Pnp
