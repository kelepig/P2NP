/-
  文件：Pnp/Machine/CopyCell.lean
  File: Pnp/Machine/CopyCell.lean

  主题：**单格镜像拷贝机**——源格 `[codeFst a, codeSnd a, some true]` 的头停在标记位时，
        把该格以 `[codeFst a, codeSnd a, some false]` 形式写到左侧三格空白，头回到标记位。
  Topic: mirror one cell into the three blanks on its left; marker `true` (copy form)
  becomes `false` (region form), head returns to the marker.

  状态布局（#168 布局表的单格特化，编号紧凑重排）：
  0 入口；1 读 `codeSnd`；2/3 读 `codeFst`（状态位存 `codeSnd` 的 bit）；
  4..7 写标记位 `false`；8..11 写 `codeSnd`；12..15 写 `codeFst`；
  16..31 右行四段回到标记位；32..35 接受；99 通用接受/拒绝。
-/

import Pnp.Machine.RegionBuild

namespace Pnp

namespace DTM

/-- **单格镜像拷贝机**（128 状态，实际用 0–35 与 99）。 -/
def copyCellL : DTM 128 where
  step := fun st a =>
    match st.val with
    | 0 =>
      (match a with
       | some true => (⟨1, by omega⟩, some true, Dir.left)
       | _ => (st, a, Dir.stay))
    | 1 =>
      (match a with
       | some b2 => (⟨2 + (match b2 with | true => 1 | false => 0), by split <;> omega⟩, some b2, Dir.left)
       | none => (st, a, Dir.stay))
    | 2 =>
      (match a with
       | some b1 => (⟨4 + (match b1 with | true => 2 | false => 0) + 0, by split <;> omega⟩, some b1, Dir.left)
       | none => (st, a, Dir.stay))
    | 3 =>
      (match a with
       | some b1 => (⟨4 + (match b1 with | true => 2 | false => 0) + 1, by split <;> omega⟩, some b1, Dir.left)
       | none => (st, a, Dir.stay))
    | 4 => (⟨8, by omega⟩, some false, Dir.left)
    | 5 => (⟨9, by omega⟩, some false, Dir.left)
    | 6 => (⟨10, by omega⟩, some false, Dir.left)
    | 7 => (⟨11, by omega⟩, some false, Dir.left)
    | 8 => (⟨12, by omega⟩, some false, Dir.left)
    | 9 => (⟨13, by omega⟩, some true, Dir.left)
    | 10 => (⟨14, by omega⟩, some false, Dir.left)
    | 11 => (⟨15, by omega⟩, some true, Dir.left)
    | 12 => (⟨16, by omega⟩, some false, Dir.right)
    | 13 => (⟨17, by omega⟩, some false, Dir.right)
    | 14 => (⟨18, by omega⟩, some true, Dir.right)
    | 15 => (⟨19, by omega⟩, some true, Dir.right)
    | 16 => (⟨20, by omega⟩, a, Dir.right)
    | 17 => (⟨21, by omega⟩, a, Dir.right)
    | 18 => (⟨22, by omega⟩, a, Dir.right)
    | 19 => (⟨23, by omega⟩, a, Dir.right)
    | 20 => (⟨24, by omega⟩, a, Dir.right)
    | 21 => (⟨25, by omega⟩, a, Dir.right)
    | 22 => (⟨26, by omega⟩, a, Dir.right)
    | 23 => (⟨27, by omega⟩, a, Dir.right)
    | 24 => (⟨28, by omega⟩, a, Dir.right)
    | 25 => (⟨29, by omega⟩, a, Dir.right)
    | 26 => (⟨30, by omega⟩, a, Dir.right)
    | 27 => (⟨31, by omega⟩, a, Dir.right)
    | 28 => (⟨32, by omega⟩, a, Dir.right)
    | 29 => (⟨33, by omega⟩, a, Dir.right)
    | 30 => (⟨34, by omega⟩, a, Dir.right)
    | 31 => (⟨35, by omega⟩, a, Dir.right)
    | 32 => (⟨99, by omega⟩, a, Dir.stay)
    | 33 => (⟨99, by omega⟩, a, Dir.stay)
    | 34 => (⟨99, by omega⟩, a, Dir.stay)
    | 35 => (⟨99, by omega⟩, a, Dir.stay)
    | _ => (st, a, Dir.stay)
  start := ⟨0, by omega⟩
  accept := ⟨99, by omega⟩
  reject := ⟨99, by omega⟩


/-- 非 99 状态一律不停机。 Non-99 states are never halted. -/
theorem copyCellL_halted_ne (st : Nat) (hst : st < 128) (h : st ≠ 99) (t : Tape) :
    copyCellL.halted ⟨⟨st, hst⟩, t⟩ = false := by
  simp only [DTM.halted, copyCellL]
  rw [Bool.or_self, beq_eq_false_iff_ne]
  intro hh
  exact h (congrArg Fin.val hh)

/-- **单步运行**（`copyCellL` 版）：给定字面量状态与读符号上的显式转移，
    `run 1` 即「写入 + 移动」后的格局。
    One explicit step of `copyCellL`. -/
theorem estepL (st : Nat) (hst : st < 128) (a : Sym) (q' : Fin 128) (s : Sym) (d : Dir)
    (h : copyCellL.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 99) :
    copyCellL.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (copyCellL_halted_ne st hst hne _)]
  exact stepConfig_of_step copyCellL ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- 单格拷贝（`codeFst` 位 0、`codeSnd` 位 0 的字面量实例）。 -/
theorem copyCellL_run_ff (M R : List Sym) :
    copyCellL.run 11
      ⟨(⟨0, by omega⟩ : Fin 128),
        Tape.mk (some false :: some false :: none :: none :: none :: M) (some true :: R)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk (some false :: some false :: some false :: some false :: some false :: M)
            (some true :: R)⟩ := by
  rw [show (11 : Nat) = 1 + 10 from rfl, DTM.run_add copyCellL 1 10]
  rw [estepL 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (10 : Nat) = 1 + 9 from rfl, DTM.run_add copyCellL 1 9]
  rw [estepL 1 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (9 : Nat) = 1 + 8 from rfl, DTM.run_add copyCellL 1 8]
  rw [estepL 2 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (8 : Nat) = 1 + 7 from rfl, DTM.run_add copyCellL 1 7]
  rw [estepL 4 (by omega) (none) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (7 : Nat) = 1 + 6 from rfl, DTM.run_add copyCellL 1 6]
  rw [estepL 8 (by omega) (none) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (6 : Nat) = 1 + 5 from rfl, DTM.run_add copyCellL 1 5]
  rw [estepL 12 (by omega) (none) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (5 : Nat) = 1 + 4 from rfl, DTM.run_add copyCellL 1 4]
  rw [estepL 16 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (4 : Nat) = 1 + 3 from rfl, DTM.run_add copyCellL 1 3]
  rw [estepL 20 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (3 : Nat) = 1 + 2 from rfl, DTM.run_add copyCellL 1 2]
  rw [estepL 24 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (2 : Nat) = 1 + 1 from rfl, DTM.run_add copyCellL 1 1]
  rw [estepL 28 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [estepL 32 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- 单格拷贝（`codeFst` 位 0、`codeSnd` 位 1 的字面量实例）。 -/
theorem copyCellL_run_ft (M R : List Sym) :
    copyCellL.run 11
      ⟨(⟨0, by omega⟩ : Fin 128),
        Tape.mk (some true :: some false :: none :: none :: none :: M) (some true :: R)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk (some true :: some false :: some false :: some true :: some false :: M)
            (some true :: R)⟩ := by
  rw [show (11 : Nat) = 1 + 10 from rfl, DTM.run_add copyCellL 1 10]
  rw [estepL 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (10 : Nat) = 1 + 9 from rfl, DTM.run_add copyCellL 1 9]
  rw [estepL 1 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (9 : Nat) = 1 + 8 from rfl, DTM.run_add copyCellL 1 8]
  rw [estepL 3 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (8 : Nat) = 1 + 7 from rfl, DTM.run_add copyCellL 1 7]
  rw [estepL 5 (by omega) (none) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (7 : Nat) = 1 + 6 from rfl, DTM.run_add copyCellL 1 6]
  rw [estepL 9 (by omega) (none) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (6 : Nat) = 1 + 5 from rfl, DTM.run_add copyCellL 1 5]
  rw [estepL 13 (by omega) (none) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (5 : Nat) = 1 + 4 from rfl, DTM.run_add copyCellL 1 4]
  rw [estepL 17 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (4 : Nat) = 1 + 3 from rfl, DTM.run_add copyCellL 1 3]
  rw [estepL 21 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (3 : Nat) = 1 + 2 from rfl, DTM.run_add copyCellL 1 2]
  rw [estepL 25 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (2 : Nat) = 1 + 1 from rfl, DTM.run_add copyCellL 1 1]
  rw [estepL 29 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [estepL 33 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- 单格拷贝（`codeFst` 位 1、`codeSnd` 位 1 的字面量实例）。 -/
theorem copyCellL_run_tt (M R : List Sym) :
    copyCellL.run 11
      ⟨(⟨0, by omega⟩ : Fin 128),
        Tape.mk (some true :: some true :: none :: none :: none :: M) (some true :: R)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk (some true :: some true :: some false :: some true :: some true :: M)
            (some true :: R)⟩ := by
  rw [show (11 : Nat) = 1 + 10 from rfl, DTM.run_add copyCellL 1 10]
  rw [estepL 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (10 : Nat) = 1 + 9 from rfl, DTM.run_add copyCellL 1 9]
  rw [estepL 1 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (9 : Nat) = 1 + 8 from rfl, DTM.run_add copyCellL 1 8]
  rw [estepL 3 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (8 : Nat) = 1 + 7 from rfl, DTM.run_add copyCellL 1 7]
  rw [estepL 7 (by omega) (none) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (7 : Nat) = 1 + 6 from rfl, DTM.run_add copyCellL 1 6]
  rw [estepL 11 (by omega) (none) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (6 : Nat) = 1 + 5 from rfl, DTM.run_add copyCellL 1 5]
  rw [estepL 15 (by omega) (none) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (5 : Nat) = 1 + 4 from rfl, DTM.run_add copyCellL 1 4]
  rw [estepL 19 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (4 : Nat) = 1 + 3 from rfl, DTM.run_add copyCellL 1 3]
  rw [estepL 23 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (3 : Nat) = 1 + 2 from rfl, DTM.run_add copyCellL 1 2]
  rw [estepL 27 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [show (2 : Nat) = 1 + 1 from rfl, DTM.run_add copyCellL 1 1]
  rw [estepL 31 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [estepL 35 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- **单格镜像拷贝机的整轮运行**（11 步）：源格 `[codeFst a, codeSnd a, some true]`
    的头停在标记位、左侧三格为空白时，把该格写成 `[codeFst a, codeSnd a, some false]`
    并回到标记位；源格左邻的符号与其余纸带不变。
    One full round (11 steps) of the mirror-copy machine. -/
theorem copyCellL_run (a : Sym) (M R : List Sym) :
    copyCellL.run 11
      ⟨(⟨0, by omega⟩ : Fin 128),
        Tape.mk (codeSnd a :: codeFst a :: none :: none :: none :: M) (some true :: R)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk (codeSnd a :: codeFst a :: some false :: codeSnd a :: codeFst a :: M)
            (some true :: R)⟩ := by
  cases a with
  | none =>
      simpa only [codeFst, codeSnd, symCode, List.drop_zero, List.drop_succ_cons,
        List.headD_cons] using copyCellL_run_ff M R
  | some b => cases b with
    | false =>
        simpa only [codeFst, codeSnd, symCode, List.drop_zero, List.drop_succ_cons,
        List.headD_cons] using copyCellL_run_ft M R
    | true =>
        simpa only [codeFst, codeSnd, symCode, List.drop_zero, List.drop_succ_cons,
        List.headD_cons] using copyCellL_run_tt M R


/-! ### 整段标记位翻转机 `flipCells`（`true → false`，右向扫描） -/

/-- **整段标记位翻转机**：把 `codeCells (cs.map (·,true))` 逐格改写成
    `codeCells (cs.map (·,false))`，头从左端扫到块后空白并接受。
    Flips every marker bit from `true` to `false` while scanning right.
    状态：1 = 格首（codeFst 位）；2 = codeSnd 位；0 = 标记位（写 `some false`）；99 接受。 -/
def flipCells : DTM 128 where
  step := fun st a =>
    match st.val with
    | 0 => (match a with
       | some true => (⟨1, by omega⟩, some false, Dir.right)
       | _ => (⟨99, by omega⟩, a, Dir.stay))
    | 1 => (match a with
       | none => (⟨99, by omega⟩, none, Dir.stay)
       | some _ => (⟨2, by omega⟩, a, Dir.right))
    | 2 => (⟨0, by omega⟩, a, Dir.right)
    | _ => (st, a, Dir.stay)
  start := ⟨1, by omega⟩
  accept := ⟨99, by omega⟩
  reject := ⟨99, by omega⟩

/-- 非 99 状态一律不停机。 Non-99 states never halt. -/
theorem flipCells_halted_ne (st : Nat) (hst : st < 128) (h : st ≠ 99) (t : Tape) :
    flipCells.halted ⟨⟨st, hst⟩, t⟩ = false := by
  simp only [DTM.halted, flipCells]
  rw [Bool.or_self, beq_eq_false_iff_ne]
  intro hh
  exact h (congrArg Fin.val hh)

/-- `flipCells` 的单步运行套路（与 `estepL` 同形）。
    The one-step idiom for `flipCells`, shaped like `estepL`. -/
theorem estepF (st : Nat) (hst : st < 128) (a : Sym) (q' : Fin 128) (s : Sym) (d : Dir)
    (h : flipCells.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 99) :
    flipCells.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (flipCells_halted_ne st hst hne _)]
  exact stepConfig_of_step flipCells ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- **单格翻转（3 步）**：把一格 `[codeFst a, codeSnd a, some true]` 的标记位翻成
    `some false`，头右移到下一格首。
    Flip one cell (3 steps) and move the head to the next cell. -/
theorem flipOne (a : Sym) (L R : List Sym) (h1 : 1 < 128) :
    flipCells.run 3
      ⟨⟨1, h1⟩, Tape.mk L (codeFst a :: codeSnd a :: some true :: R)⟩
      = ⟨⟨1, h1⟩, Tape.mk (some false :: codeSnd a :: codeFst a :: L) R⟩ := by
  cases a with
  | none =>
      simp only [codeFst, codeSnd, symCode, List.headD_cons, List.drop_zero,
        List.drop_succ_cons]
      rw [show (3 : Nat) = 1 + (1 + 1) from rfl, DTM.run_add flipCells 1 (1 + 1)]
      rw [estepF 1 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [DTM.run_add flipCells 1 1]
      rw [estepF 2 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [estepF 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
      etape
  | some b => cases b with
    | false =>
        simp only [codeFst, codeSnd, symCode, List.headD_cons, List.drop_zero,
          List.drop_succ_cons]
        rw [show (3 : Nat) = 1 + (1 + 1) from rfl, DTM.run_add flipCells 1 (1 + 1)]
        rw [estepF 1 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
        etape
        rw [DTM.run_add flipCells 1 1]
        rw [estepF 2 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
        etape
        rw [estepF 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
        etape
    | true =>
        simp only [codeFst, codeSnd, symCode, List.headD_cons, List.drop_zero,
          List.drop_succ_cons]
        rw [show (3 : Nat) = 1 + (1 + 1) from rfl, DTM.run_add flipCells 1 (1 + 1)]
        rw [estepF 1 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
        etape
        rw [DTM.run_add flipCells 1 1]
        rw [estepF 2 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
        etape
        rw [estepF 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
        etape


/-- 标记位为 1 的格编码展开成三个符号。 A `true`-marker cell code as three symbols. -/
theorem cellCode_true_eq (a : Sym) :
    cellCode (a, true) = [codeFst a, codeSnd a, some true] := by
  simp [cellCode, symCode_eq]

/-- 标记位为 0 的格编码展开成三个符号。 A `false`-marker cell code as three symbols. -/
theorem cellCode_false_eq (a : Sym) :
    cellCode (a, false) = [codeFst a, codeSnd a, some false] := by
  simp [cellCode, symCode_eq]

/-- **整段标记位翻转**：把 `n` 个 `true` 标记格逐格翻成 `false`，头停到块后空白。
    步数 `3n + 1`（每格 3 步 + 末尾接受 1 步）。
    Flip all `n` marker bits from `true` to `false`; head ends on the blank after the block. -/
theorem flipCells_run (cs : List Sym) (L R : List Sym) :
    flipCells.run (3 * cs.length + 1)
      ⟨(⟨1, by omega⟩ : Fin 128),
        Tape.mk L (codeCells (cs.map (fun a => (a, true))) ++ none :: R)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk ((codeCells (cs.map (fun a => (a, false)))).reverse ++ L) (none :: R)⟩ := by
  induction cs generalizing L with
  | nil =>
      simp only [List.map_nil, codeCells, List.flatMap_nil, List.nil_append]
      rw [show 3 * ([] : List Sym).length + 1 = 1 from rfl]
      rw [estepF 1 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
      etape
      rfl
  | cons a t ih =>
      simp only [List.map_cons, codeCells_cons, cellCode_true_eq, cellCode_false_eq,
        List.cons_append, List.append_assoc, List.nil_append, List.singleton_append]
      rw [show 3 * (a :: t).length + 1 = 3 + (3 * t.length + 1) from by
            simp only [List.length_cons]; omega]
      rw [DTM.run_add flipCells 3 (3 * t.length + 1)]
      rw [flipOne a L (codeCells (List.map (fun a => (a, true)) t) ++ none :: R) (by omega)]
      rw [ih (L := some false :: codeSnd a :: codeFst a :: L)]
      simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append, List.append_assoc, List.singleton_append]


/-! ### 整块拷贝的走位件（跨过已写格块） -/

/-- 左带是「已写格块的逆序」时，左移 `3n` 步正好跨过整块。
    Walking left across a full written cell block (`3n` symbols). -/
theorem moveLeftN_codeCells (cs : List (Sym × Bool)) (L R : List Sym) :
    moveLeftN (3 * cs.length) ⟨(codeCells cs).reverse ++ L, R⟩
      = ⟨L, codeCells cs ++ R⟩ := by
  rw [moveLeftN_append _ _ _ _ (by
      simp only [List.length_append, List.length_reverse, codeCells_length]; omega)]
  rw [show (3 * cs.length) = ((codeCells cs).reverse).length from by
        rw [List.length_reverse, codeCells_length]]
  rw [List.drop_length, List.take_length, List.reverse_reverse, List.nil_append]


/-- 右移跨过任意符号串：`moveRightN |l| ⟨L, l ++ R⟩ = ⟨l.reverse ++ L, R⟩`。
    Walking right across any symbol string of matching length. -/
theorem moveRightN_of_length : ∀ (l : List Sym) (L R : List Sym),
    moveRightN l.length ⟨L, l ++ R⟩ = ⟨l.reverse ++ L, R⟩
  | [], _, _ => rfl
  | a :: t, L, R => by
      rw [show (a :: t).length = 1 + t.length from by
            simp only [List.length_cons]; omega]
      rw [moveRightN_add 1 t.length]
      rw [show moveRightN 1 (⟨L, (a :: t) ++ R⟩ : Tape) = ⟨a :: L, t ++ R⟩ from rfl]
      rw [moveRightN_of_length t (a :: L) R]
      simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

/-- 右移跨过整块已写格（`3n` 个符号）。 Walking right across a whole written cell block. -/
theorem moveRightN_codeCells (cs : List (Sym × Bool)) (L R : List Sym) :
    moveRightN (3 * cs.length) ⟨L, codeCells cs ++ R⟩
      = ⟨(codeCells cs).reverse ++ L, R⟩ := by
  rw [← codeCells_length cs]
  exact moveRightN_of_length (codeCells cs) L R


/-! ### 自适应走位机 `walkL` / `walkR`（无计数器，读到空白即停） -/

/-- **左走机**：连续左移，直到读到空白（或左带耗尽时补出的空白）为止。
    A left-walking machine: keep moving left until a blank is read. -/
def walkL : DTM 128 where
  step := fun st a =>
    match st.val with
    | 0 => (match a with
       | none => (⟨99, by omega⟩, none, Dir.stay)
       | some _ => (⟨0, by omega⟩, a, Dir.left))
    | _ => (st, a, Dir.stay)
  start := ⟨0, by omega⟩
  accept := ⟨99, by omega⟩
  reject := ⟨99, by omega⟩

/-- 非 99 状态一律不停机。 Non-99 states never halt. -/
theorem walkL_halted_ne (st : Nat) (hst : st < 128) (h : st ≠ 99) (t : Tape) :
    walkL.halted ⟨⟨st, hst⟩, t⟩ = false := by
  simp only [DTM.halted, walkL]
  rw [Bool.or_self, beq_eq_false_iff_ne]
  intro hh
  exact h (congrArg Fin.val hh)

/-- `walkL` 的单步运行套路。 The one-step idiom for `walkL`. -/
theorem estepWL (st : Nat) (hst : st < 128) (a : Sym) (q' : Fin 128) (s : Sym) (d : Dir)
    (h : walkL.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 99) :
    walkL.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (walkL_halted_ne st hst hne _)]
  exact stepConfig_of_step walkL ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- **左走机运行**：左带 `l` 全非空、当前读到 `some x` 时，走 `|l|+2` 步
    停在左端补出的空白上，右带为 `none :: l.reverse ++ some x :: R`。
    `walkL` run: walks to the blank left of `l` in `|l|+2` steps. -/
theorem walkL_run : ∀ (l : List Sym), (∀ y ∈ l, y ≠ none) → ∀ (x : Bool) (R : List Sym),
    walkL.run (l.length + 2)
      ⟨(⟨0, by omega⟩ : Fin 128), Tape.mk l (some x :: R)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk ([] : List Sym) (none :: l.reverse ++ some x :: R)⟩
  | [], _, x, R => by
      rw [show ([] : List Sym).length + 2 = 1 + 1 from by simp,
            DTM.run_add walkL 1 1]
      rw [estepWL 0 (by omega) (some x) _ _ _ (by rfl) _ _ (by omega)]
      etape
      rw [estepWL 0 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
      etape
      simp only [List.reverse_nil, List.nil_append]
  | a :: t, hl, x, R => by
      have ht : ∀ y ∈ t, y ≠ none := fun y hy => hl y (by simp [hy])
      cases a with
      | none => exact absurd rfl (hl none (by simp))
      | some y =>
          rw [show (some y :: t).length + 2 = 1 + (t.length + 2) from by
                simp only [List.length_cons]; omega]
          rw [DTM.run_add walkL 1 (t.length + 2)]
          rw [estepWL 0 (by omega) (some x) _ _ _ (by rfl) _ _ (by omega)]
          etape
          rw [walkL_run t ht y (some x :: R)]
          simp only [List.reverse_cons, List.append_assoc, List.nil_append]
          rfl


/-- **右走机**：连续右移，直到读到空白为止。
    A right-walking machine: keep moving right until a blank is read. -/
def walkR : DTM 128 where
  step := fun st a =>
    match st.val with
    | 0 => (match a with
       | none => (⟨99, by omega⟩, none, Dir.stay)
       | some _ => (⟨0, by omega⟩, a, Dir.right))
    | _ => (st, a, Dir.stay)
  start := ⟨0, by omega⟩
  accept := ⟨99, by omega⟩
  reject := ⟨99, by omega⟩

/-- 非 99 状态一律不停机。 Non-99 states never halt. -/
theorem walkR_halted_ne (st : Nat) (hst : st < 128) (h : st ≠ 99) (t : Tape) :
    walkR.halted ⟨⟨st, hst⟩, t⟩ = false := by
  simp only [DTM.halted, walkR]
  rw [Bool.or_self, beq_eq_false_iff_ne]
  intro hh
  exact h (congrArg Fin.val hh)

/-- `walkR` 的单步运行套路。 The one-step idiom for `walkR`. -/
theorem estepWR (st : Nat) (hst : st < 128) (a : Sym) (q' : Fin 128) (s : Sym) (d : Dir)
    (h : walkR.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 99) :
    walkR.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (walkR_halted_ne st hst hne _)]
  exact stepConfig_of_step walkR ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- **右走机运行**：右带 `l ++ none :: R`（`l` 全非空）时，走 `|l|+1` 步
    停在块后空白上，左带累积 `l.reverse`。
    `walkR` run: walks to the blank after `l` in `|l|+1` steps. -/
theorem walkR_run : ∀ (l : List Sym), (∀ y ∈ l, y ≠ none) → ∀ (L R : List Sym),
    walkR.run (l.length + 1)
      ⟨(⟨0, by omega⟩ : Fin 128), Tape.mk L (l ++ none :: R)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk (l.reverse ++ L) (none :: R)⟩
  | [], _, L, R => by
      rw [show ([] : List Sym).length + 1 = 1 from by simp]
      simp only [List.nil_append, List.reverse_nil]
      rw [estepWR 0 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
      etape
  | a :: t, hl, L, R => by
      have ht : ∀ y ∈ t, y ≠ none := fun y hy => hl y (by simp [hy])
      cases a with
      | none => exact absurd rfl (hl none (by simp))
      | some y =>
          rw [show (some y :: t).length + 1 = 1 + (t.length + 1) from by
                simp only [List.length_cons]; omega]
          rw [DTM.run_add walkR 1 (t.length + 1)]
          rw [show ((some y :: t) ++ none :: R) = some y :: (t ++ none :: R) from rfl]
          rw [estepWR 0 (by omega) (some y) _ _ _ (by rfl) _ _ (by omega)]
          etape
          rw [show Tape.mk (some y :: L) (t ++ none :: R)
                = Tape.mk (some y :: L) (t ++ (none :: R)) from rfl]
          rw [walkR_run t ht (some y :: L) R]
          simp only [List.reverse_cons, List.append_assoc, List.singleton_append]

end DTM

end Pnp
