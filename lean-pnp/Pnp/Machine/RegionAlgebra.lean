/-
  文件：Pnp/Machine/RegionAlgebra.lean
  File: Pnp/Machine/RegionAlgebra.lean

  主题：**区域编码的代数组件**——格标记符号 `cellMark`、单格编码的逆序三联
        `cellRev`、整块逆序 `codeCells_reverse_eq`，以及「区域扁平形态 ↔ `Reg.enc`」
        的桥接恒等式 `enc_flat` / `enc_flat_reverse`；配套的收尾机 `markHead`
        （把当前格标记位由 `some false` 翻成 `some true` 后原地停机）。
  Topic: algebraic components of the region encoding — the marker symbol `cellMark`, the
  reversed cell triple `cellRev`, the block reversal identity, the flat-form bridge to
  `Reg.enc`, and the marker-writing finishing machine `markHead`.

  本文件给出：
    - `cellMark` / `cellCode_eq_append` / `cellCode_reverse` / `cellRev`；
    - `codeCells_reverse_eq`：`(codeCells xs).reverse = xs.reverse.flatMap cellRev`；
    - `codeCells_split_reverse`：把 `pre ++ [p] ++ post` 的逆序拆成三段；
    - `enc_flat`（定义展开）与 `enc_flat_reverse`（扁平逆序 ⇒ 编码逆序的桥）；
    - `flat_moveLeft`：自扁平块右端左移 `3|post|` 步（`moveLeftN_codeCells` 的应用）；
    - `markHead` 机器与 `markHead_run`：把当前格标记位翻成 `some true`。
  This file gives the marker algebra, the flat/reversed bridges, and the marker machine.
-/

import Pnp.Machine.SimRegion
import Pnp.Machine.CopyCell

namespace Pnp

namespace DTM

/-! ### 格标记与单格编码的逆序三联 -/

/-- 格标记符号：标记位 `true` 记作 `some true`、`false` 记作 `some false`。
    The marker symbol attached to a cell's flag bit. -/
def cellMark (b : Bool) : Sym := if b then some true else some false

@[simp] theorem cellMark_true : cellMark true = some true := rfl

@[simp] theorem cellMark_false : cellMark false = some false := rfl

/-- 单格编码展开成「两个符号编码 ++ 标记位」。
    A single cell code splits into its two symbol codes plus the marker. -/
theorem cellCode_eq_append (p : Sym × Bool) :
    cellCode p = codeFst p.1 :: codeSnd p.1 :: [cellMark p.2] := by
  obtain ⟨a, b⟩ := p
  cases a with
  | none => rfl
  | some c => cases c <;> rfl

/-- 单格编码的逆序：标记位在前，随后 `codeSnd`、`codeFst`（物理左带上的读法）。
    The reversed cell code: marker first, then `codeSnd`, then `codeFst`. -/
theorem cellCode_reverse (p : Sym × Bool) :
    (cellCode p).reverse = cellMark p.2 :: codeSnd p.1 :: [codeFst p.1] := by
  rw [cellCode_eq_append]
  rfl

/-- 格的「逆序三联」简写。 Shorthand for the reversed cell triple. -/
def cellRev (p : Sym × Bool) : List Sym := [cellMark p.2, codeSnd p.1, codeFst p.1]

/-- 逆序三联就是单格编码的逆序。 `cellRev` is the reversal of `cellCode`. -/
theorem cellRev_eq (p : Sym × Bool) : cellRev p = (cellCode p).reverse := by
  rw [cellRev, cellCode_reverse]

/-- **整块逆序**：整块编码的逆序 = 格列表逆序后逐格取逆序三联。
    Whole-block reversal: reverse the cell list and use `cellRev` per cell. -/
theorem codeCells_reverse_eq (xs : List (Sym × Bool)) :
    (codeCells xs).reverse = xs.reverse.flatMap cellRev := by
  induction xs with
  | nil => rfl
  | cons p ps ih =>
      rw [codeCells, List.flatMap_cons, List.reverse_append, List.reverse_cons,
        List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      rw [← ih, cellRev_eq]
      simp only [codeCells]

/-- **三段拆分**：`pre ++ [p] ++ post` 的逆序 = `post` 逆序 ++ `p` 的逆序三联 ++ `pre` 逆序。
    Splitting the reversal at a designated cell. -/
theorem codeCells_split_reverse (pre post : List (Sym × Bool)) (p : Sym × Bool) :
    (codeCells (pre ++ [p] ++ post)).reverse
      = (codeCells post).reverse ++ cellRev p ++ (codeCells pre).reverse := by
  rw [codeCells_append, codeCells_append,
    show codeCells [p] = cellCode p from by simp [codeCells],
    cellRev_eq, List.reverse_append, List.reverse_append]
  simp only [List.append_assoc]

/-! ### 扁平形态与 `Reg.enc` 的桥 -/

/-- `Reg.enc` 的定义展开（左侧两符号编码 + 前缀逆序，右侧头标记 + 后缀格）。
    Definition unfolding of `Reg.enc`. -/
theorem enc_flat {q : Nat} (x : Reg q) (L : List Sym) :
    Reg.enc x L
      = Tape.mk (codeSnd x.cur :: codeFst x.cur :: ((codeCells x.pre).reverse ++ L))
          (some true :: codeCells x.post) := rfl

/-- **扁平逆序 ⇒ 编码逆序**：把区域格串 `pre ++ [cur] ++ post` 的逆序写成
    「`post` 逆序 ++ 当前格标记 `some false` ++ 头部左带」，便于直接对接转写机输出。
    Bridge from the flat reversed form of a whole region to the encoded left tape. -/
theorem enc_flat_reverse {q : Nat} (x : Reg q) (L : List Sym) :
    (codeCells (x.pre ++ [(x.cur, false)] ++ x.post)).reverse ++ L
      = (codeCells x.post).reverse ++ some false ::
          (codeSnd x.cur :: codeFst x.cur :: ((codeCells x.pre).reverse ++ L)) := by
  rw [codeCells_split_reverse, cellRev, cellMark_false]
  simp only [List.cons_append, List.append_assoc, List.nil_append]

/-- **扁平左移**：在扁平形态上自块右端左移 `3|post|` 步，跨过 `post` 的逆序段，
    头停到当前格标记位左侧一格，`post` 原序回到右带。
    Walking left across the reversed `post` segment of the flat form. -/
theorem flat_moveLeft {q : Nat} (x : Reg q) (L2 tail : List Sym) :
    moveLeftN (3 * x.post.length)
      ⟨(codeCells (x.pre ++ [(x.cur, false)] ++ x.post)).reverse ++ L2, none :: tail⟩
      = ⟨some false :: (codeSnd x.cur :: codeFst x.cur :: ((codeCells x.pre).reverse ++ L2)),
          codeCells x.post ++ none :: tail⟩ := by
  rw [enc_flat_reverse x L2]
  exact moveLeftN_codeCells x.post
    (some false :: (codeSnd x.cur :: codeFst x.cur :: ((codeCells x.pre).reverse ++ L2)))
    (none :: tail)

/-! ### 收尾机 `markHead` -/

/-- **写头标记机**（两状态）：把当前符号改写成 `some true` 并原地停机。
    `Reg.enc` 的收尾动作：头停在当前格标记位上（标记原为 `some false`）。
    The marker machine: overwrite the current symbol by `some true` and halt in place. -/
def markHead : DTM 2 where
  step := fun _ _ => (⟨1, by omega⟩, some true, Dir.stay)
  start := ⟨0, by omega⟩
  accept := ⟨1, by omega⟩
  reject := ⟨1, by omega⟩

/-- 起始状态不是终止态。 The start state is not terminal. -/
theorem markHead_halted_zero (t : Tape) : markHead.halted ⟨(⟨0, by omega⟩ : Fin 2), t⟩ = false := by
  simp [DTM.halted, markHead]

/-- **一步运行**：读 `a`、写 `some true`、原地停在接受态。
    One-step run: read `a`, write `some true`, halt in place. -/
theorem markHead_run (L : List Sym) (a : Sym) (R : List Sym) :
    markHead.run 1 ⟨markHead.start, Tape.mk L (a :: R)⟩
      = ⟨markHead.accept, Tape.mk L (some true :: R)⟩ := by
  have hnh : markHead.halted ⟨markHead.start, Tape.mk L (a :: R)⟩ = false := by
    simp [DTM.halted, markHead]
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted markHead 0 _ hnh]
  show markHead.stepConfig ⟨(⟨0, by omega⟩ : Fin 2), Tape.mk L (a :: R)⟩
      = ⟨(⟨1, by omega⟩ : Fin 2), Tape.mk L (some true :: R)⟩
  simp only [DTM.stepConfig, markHead, Tape.read, Tape.write, Tape.move]
  rfl

end DTM

end Pnp
