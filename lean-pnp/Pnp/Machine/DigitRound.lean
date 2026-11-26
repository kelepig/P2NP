/-
  文件：Pnp/Machine/DigitRound.lean
  File: Pnp/Machine/DigitRound.lean

  主题：把 `incDigit`（#278）的两条单轮规格抬到**数字区序列**层。
  Topic: lift the two single-round specs of `incDigit` (#278) to the digit-sequence level.

  数字区的纸带约定（B5 外层枚举 E 的计数器）：
  - 低位在右。`ds : List Nat` 按「从右往左」存数字，`ds.head` 是最右（最低位）块；
  - 头停在区域终止空白上，故头部**左侧**的格序恰为「最低位块的反序 ++ 次低位块的反序 ++ …」，
    即 `areaL ds = (blockCode ds₀).reverse ++ (blockCode ds₁).reverse ++ …`；
  - 一轮加一：最低位未满（`d+1 < B`）就把块加长一格（`incDigit_round_grow`）；
    最低位已满（`d+1 = B`）就弹掉该块，弹出的真格留成**右侧垃圾**（`incDigit_round_pop`），
    于是下一轮的「最右活块」自动变成原来的次低位块——进位因此可以逐轮完成。
  Tape convention: the head sits on the area's trailing blank, so the cells to its left are
  the blocks of `ds` in reverse per-block order (`areaL`). One round either grows the lowest
  block or pops it, leaving the popped cells as garbage on the right; the next round then
  targets the next live block, so carries need no extra machine.
-/

import Pnp.Machine.DigitInc

namespace Pnp

namespace DTM

/-- 数字序列的头左侧格串：最低位块反序 ++ 次低位块反序 ++ …
    The cells to the left of the head, in per-block reverse order. -/
def areaL : List Nat → List Sym
  | [] => []
  | d :: ds => (blockCode d).reverse ++ areaL ds

/-- `areaL` 的展开式。 Unfolding of `areaL` on a cons. -/
theorem areaL_cons (d : Nat) (ds : List Nat) :
    areaL (d :: ds) = (blockCode d).reverse ++ areaL ds := rfl

/-- 把序列头拆成「真格串 + 块首 + 余下块」，供与 `incDigit` 的纸带形态对齐。
    Splitting the front block off, to match the tape shapes used by `incDigit`. -/
theorem areaL_head_append (d : Nat) (ds : List Nat) (L : List Sym) :
    areaL (d :: ds) ++ L
      = List.replicate (d + 2) (some true) ++ some false :: (areaL ds ++ L) := by
  simp [areaL_cons, blockCode, List.append_assoc]

/-- **不进位的一轮**：最低位 `d`（`d+1 < B`）加一，头回新的终止空白。
    One round without carry: the lowest digit grows by one. -/
theorem incDigit_round_grow (B d : Nat) (hd : d + 1 < B) (ds : List Nat)
    (L G : List Sym) :
    (incDigit B).run (2 * d + 10)
        (Config.mk (⟨0, by omega⟩ : Fin (B + 7))
          (Tape.mk (areaL (d :: ds) ++ L) (none :: G))) =
      Config.mk (⟨B + 6, by omega⟩ : Fin (B + 7))
        (Tape.mk (areaL ((d + 1) :: ds) ++ L) (none :: G.tail)) := by
  rw [areaL_head_append, areaL_head_append]
  exact incDigit_run_grow B d hd (areaL ds ++ L) G

/-- **进位的一轮**：最低位已满（`d+1 = B`），弹掉该块，弹出的真格成右侧垃圾。
    One round with carry: the full lowest block is popped and its cells become right garbage. -/
theorem incDigit_round_pop (B d : Nat) (hB : 0 < B) (hd : d + 1 = B) (ds : List Nat)
    (L G : List Sym) :
    (incDigit B).run (d + 4)
        (Config.mk (⟨0, by omega⟩ : Fin (B + 7))
          (Tape.mk (areaL (d :: ds) ++ L) (none :: G))) =
      Config.mk (⟨B + 6, by omega⟩ : Fin (B + 7))
        (Tape.mk (areaL ds ++ L)
          (none :: List.replicate (d + 2) (some true) ++ none :: G)) := by
  rw [areaL_head_append]
  exact incDigit_run_carry B d hB hd (areaL ds ++ L) G

end DTM

end Pnp
