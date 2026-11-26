/-
  文件：Pnp/Machine/ExpandEnc.lean
  File: Pnp/Machine/ExpandEnc.lean

  主题：**展开机输出 ⇒ 区域编码**——把非空白符号块 `a :: l'` 展开成格编码后，
        左移 `3|l'|` 步把读写头移到首格标记位、再左移一格并写头标记，得到
        `Reg.enc` 形态（区域前缀为空、当前格是首格、后缀是其余格）。
  Topic: from the expansion machine's output to `Reg.enc` — after expanding a non-blank
  block, walk left onto the first cell's marker, step one further left, and write the head
  marker.

  本文件给出：
    - `expand_flat`：`expand_run_cells` 的链式引用名（展开输出 = 扁平格编码逆序）；
    - `flat_left_to_marker`：扁平形态左移 `3|l'|` 步落在首格标记左侧一格；
    - `flat_to_enc`：再左移一格并写 `some true`，得到编码形态；
    - `expand_to_enc`：两段合成（纸带级）；
    - `expand_to_enc_form`：结论改写成 `Reg.enc` 的左右分量（便于外层装配引用）。
  This file chains the expander's output into `Reg.enc`, in tape form and in `Reg.enc` form.
-/

import Pnp.Machine.RegionAlgebra
import Pnp.Machine.RegionBuild
import Pnp.Machine.ExpandRun

namespace Pnp

namespace DTM

/-- 展开输出即扁平格编码形态（`expand_run_cells` 的引用名）。
    The expander's output is the flat cell-code form. -/
theorem expand_flat (a : Sym) (l' : List Sym) (hl : ∀ v ∈ a :: l', v ≠ none)
    (M R : List Sym) :
    expand.run (expandCost (a :: l'))
      ⟨(⟨0, by omega⟩ : Fin 128),
        Tape.mk M ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none ++ R)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk (List.reverse (codeCells ((a :: l').map (fun s => (s, false)))) ++ M)
            (none :: R)⟩ :=
  expand_run_cells (a :: l') hl M R

/-- 逆序三联并入左带：`… ++ cellRev p ++ ([] ++ M) = … ++ marker :: codeSnd :: codeFst :: M`。
    Absorbing a reversed cell triple into the left tape. -/
theorem append_cellRev_cons (post : List (Sym × Bool)) (p : Sym × Bool) (M : List Sym) :
    (codeCells post).reverse ++ cellRev p ++ (codeCells []).reverse ++ M
      = (codeCells post).reverse ++ cellMark p.2 :: codeSnd p.1 :: codeFst p.1 :: M := by
  simp [cellRev, codeCells]

/-- 扁平形态左移 `3|l'|` 步：跨过除首格外的所有格，头停到首格标记左侧一格。
    Walking left `3|l'|` steps in the flat form lands just left of the first cell's marker. -/
theorem flat_left_to_marker (a : Sym) (l' : List Sym) (M R : List Sym) :
    moveLeftN (3 * l'.length)
      ⟨List.reverse (codeCells ((a :: l').map (fun s => (s, false)))) ++ M, none :: R⟩
      = ⟨some false :: (codeSnd a :: codeFst a :: M),
          codeCells (l'.map (fun s => (s, false))) ++ none :: R⟩ := by
  -- 把首格单独拆出来：格列表 = `[(a,false)] ++ 其余`
  have hsplit := codeCells_split_reverse ([] : List (Sym × Bool))
    (l'.map (fun s => (s, false))) (a, false)
  rw [show ((a :: l').map (fun s => (s, false)))
        = (a, false) :: l'.map (fun s => (s, false)) from rfl]
  rw [show ((a, false) :: l'.map (fun s => (s, false)))
        = ([] : List (Sym × Bool)) ++ [(a, false)] ++ l'.map (fun s => (s, false)) from rfl]
  -- 逆序三联并入左带，得到「左移跨过整块」所需的形状
  rw [hsplit, append_cellRev_cons]
  -- 步数量纲对齐后交给「左移跨过整块」
  rw [show 3 * l'.length = 3 * (l'.map (fun s => (s, false))).length from by
        rw [List.length_map]]
  exact moveLeftN_codeCells (l'.map (fun s => (s, false)))
    (some false :: codeSnd a :: codeFst a :: M) (none :: R)

/-- 再左移一格（头落到首格标记位）并写头标记 `some true`：得到编码形态。
    One more left step onto the marker, then write `some true`. -/
theorem flat_to_enc (a : Sym) (l' : List Sym) (M R : List Sym) :
    markHead.run 1 ⟨markHead.start,
        Tape.moveLeft ⟨some false :: (codeSnd a :: codeFst a :: M),
          codeCells (l'.map (fun s => (s, false))) ++ none :: R⟩⟩
      = ⟨markHead.accept,
          Tape.mk (codeSnd a :: codeFst a :: M)
            (some true :: codeCells (l'.map (fun s => (s, false))) ++ none :: R)⟩ := by
  rw [show Tape.moveLeft ⟨some false :: (codeSnd a :: codeFst a :: M),
            codeCells (l'.map (fun s => (s, false))) ++ none :: R⟩
        = ⟨codeSnd a :: codeFst a :: M,
            some false :: codeCells (l'.map (fun s => (s, false))) ++ none :: R⟩ from rfl]
  exact markHead_run (codeSnd a :: codeFst a :: M) (some false) _

/-- **展开 ⇒ 编码形态**（纸带级）：块 `a :: l'` 展开后左移 `3|l'| + 1` 步并写头标记。
    Expansion plus head placement, at tape level. -/
theorem expand_to_enc (a : Sym) (l' : List Sym)
    (hl : ∀ v ∈ a :: l', v ≠ none) (M R : List Sym) :
    markHead.run 1 ⟨markHead.start,
        Tape.moveLeft (moveLeftN (3 * l'.length)
          (expand.run (expandCost (a :: l'))
            ⟨(⟨0, by omega⟩ : Fin 128),
              Tape.mk M ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none ++ R)⟩).tape)⟩
      = ⟨markHead.accept,
          Tape.mk (codeSnd a :: codeFst a :: M)
            (some true :: codeCells (l'.map (fun s => (s, false))) ++ none :: R)⟩ := by
  rw [expand_flat a l' hl M R]
  rw [flat_left_to_marker a l' M R]
  exact flat_to_enc a l' M R

/-- **展开 ⇒ `Reg.enc`**：结论改写成 `Reg.enc` 的左右分量，供外层装配直接引用。
    The same result phrased through `Reg.enc` (empty prefix, head on the first cell). -/
theorem expand_to_enc_form {q : Nat} (st : Fin q) (a : Sym) (l' : List Sym)
    (hl : ∀ v ∈ a :: l', v ≠ none) (M R : List Sym) :
    markHead.run 1 ⟨markHead.start,
        Tape.moveLeft (moveLeftN (3 * l'.length)
          (expand.run (expandCost (a :: l'))
            ⟨(⟨0, by omega⟩ : Fin 128),
              Tape.mk M ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none ++ R)⟩).tape)⟩
      = ⟨markHead.accept,
          Tape.mk ((Reg.enc (⟨st, [], a, l'.map (fun s => (s, false))⟩ : Reg q) M).left)
            ((Reg.enc (⟨st, [], a, l'.map (fun s => (s, false))⟩ : Reg q) M).right ++
              none :: R)⟩ := by
  rw [expand_to_enc a l' hl M R]
  rw [enc_flat]
  simp only [codeCells, List.flatMap_nil, List.reverse_nil, List.nil_append, List.cons_append]

end DTM

end Pnp
