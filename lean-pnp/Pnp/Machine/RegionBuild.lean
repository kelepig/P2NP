/-
  文件：Pnp/Machine/RegionBuild.lean
  File: Pnp/Machine/RegionBuild.lean

  主题：**区域（`Reg.enc`）与机器件输出的规格对接**——把「初始区域的物理解码」写成
        与 `padLeft` / `expand` 输出同形的列表表达式，作为 `writeRegion` 的验收目标。
  Topic: specification glue between the region encoding `Reg.enc` and the machine pieces:
  the physical form of the initial region, matched against `padLeft` / `expand` outputs.

  已定的两条对接（本文件证明）：
    1. 空白格的格编码 = 三个 `some false`，即 `padStr`（`padLeft` 写出的预留空白段）；
    2. `Reg.enc (Reg.initReg st w P P) L` 的显式形态：左列 = 首格 `codeSnd/codeFst` + 预留段逆序 + L，
       右列 = 头标记 + 其余格编码 + 右侧预留段。
  Two matches: blank cells code as three `some false` (i.e. `padStr`), and the explicit
  physical form of `Reg.enc` for the padded initial region.
-/

import Pnp.Machine.SimRegion
import Pnp.Machine.PadVerdict
import Pnp.Machine.ExpandRun

namespace Pnp

namespace DTM

/-- 空白格（标记位 0）的格编码是三个 `some false`，正好是 `padStr` 的一格。
    A blank cell (marker 0) codes as three `some false`, i.e. one cell of `padStr`. -/
theorem codeCells_replicate_none (P : Nat) :
    codeCells (List.replicate P ((none : Sym), false)) = List.replicate (3 * P) (some false) := by
  induction P with
  | zero => rfl
  | succ P ih =>
      show cellCode ((none : Sym), false) ++ codeCells (List.replicate P ((none : Sym), false))
        = List.replicate (3 * (P + 1)) (some false)
      rw [ih]
      simp only [cellCode, symCode, List.singleton_append, List.nil_append, Bool.false_eq_true,
        ite_false, List.replicate_succ]
      rfl

/-- `padLeft` 的预留空白段 `padStr T` = `T+1` 个空白格的格编码。
    The pad `padStr T` is the cell code of `T+1` blank cells. -/
theorem codeCells_replicate_none_padStr (T : Nat) :
    codeCells (List.replicate (T + 1) ((none : Sym), false)) = padStr T :=
  codeCells_replicate_none (T + 1)

/-- 初始区域编码的显式形态（把头格拆成 `codeSnd`/`codeFst` 两项，右侧写出头标记）。
    Explicit physical form of the padded initial region's encoding. -/
theorem enc_initReg_eq {q : Nat} (st : Fin q) (w : List Bool) (P : Nat) (L : List Sym) :
    Reg.enc (Reg.initReg st w P P) L =
      Tape.mk (codeSnd ((w.map some).headD none) :: codeFst ((w.map some).headD none) ::
          (List.reverse (codeCells (List.replicate P ((none : Sym), false))) ++ L))
        (some true :: codeCells ((((w.map some).drop 1).map (fun s => (s, false))) ++
          List.replicate P ((none : Sym), false))) := rfl

/-- 用 `padStr` 改写的初始区域形态：左侧预留段即 `reverse (padStr T)`，
    右侧尾部预留段是 `3(T+1)` 个 `some false`（与 `padLeft` 的输出同形）。
    Same shape with `padStr`: the left pad is `reverse (padStr T)`, the right pad is
    `3(T+1)` copies of `some false`, matching the output of `padLeft`. -/
theorem enc_initReg_eq_padStr {q : Nat} (st : Fin q) (w : List Bool) (T : Nat) (L : List Sym) :
    Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L =
      Tape.mk (codeSnd ((w.map some).headD none) :: codeFst ((w.map some).headD none) ::
          (List.reverse (padStr T) ++ L))
        (some true ::
          (codeCells (((w.map some).drop 1).map (fun s => (s, false)))
            ++ List.replicate (3 * (T + 1)) (some false))) := by
  rw [enc_initReg_eq]
  rw [codeCells_replicate_none (T + 1)]
  simp only [codeCells, List.flatMap_append]
  rw [show List.flatMap cellCode (List.replicate (T + 1) ((none : Sym), false))
        = List.replicate (3 * (T + 1)) (some false) from codeCells_replicate_none (T + 1)]
  rfl

/-- `expand_run` 的格编码形态：输出左带即格序列编码串的逆序。
    `expand_run` in cell-code form: the left tape is the reverse of the cell-code string. -/
theorem expand_run_cells (l : List Sym) (hl : ∀ v ∈ l, v ≠ none) (M R : List Sym) :
    expand.run (expandCost l)
      ⟨(⟨0, by omega⟩ : Fin 128),
        Tape.mk M (l ++ List.replicate (2 * l.length + 1) none ++ R)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk (List.reverse (codeCells (l.map (fun s => (s, false)))) ++ M) (none :: R)⟩ := by
  rw [expand_run l hl M R, codesRev_eq_reverse_codeCells]

/-! ### 右移定位件（区域铺设用） -/

/-- 连续右移 `k` 次（零依赖版迭代，避免依赖 Mathlib 的 `Function.iterate`）。
    Move right `k` times; a zero-dependency iteration. -/
def moveRightN : Nat → Tape → Tape
  | 0, t => t
  | k + 1, t => moveRightN k (Tape.moveRight t)

/-- 在 `k` 个相同符号上连续右移 `k` 次：头落到 `R` 的首符号，符号全部压进左带。
    Moving right `k` times across `k` copies of `c` pushes them onto the left tape. -/
theorem moveRightN_replicate (k : Nat) (L : List Sym) (c : Sym) (R : List Sym) :
    moveRightN k ⟨L, List.replicate k c ++ R⟩ = ⟨List.replicate k c ++ L, R⟩ := by
  induction k generalizing L with
  | zero => rfl
  | succ k ih =>
      rw [show moveRightN (k + 1) ⟨L, List.replicate (k + 1) c ++ R⟩
            = moveRightN k (Tape.moveRight ⟨L, List.replicate (k + 1) c ++ R⟩) from rfl]
      rw [show Tape.moveRight ⟨L, List.replicate (k + 1) c ++ R⟩
            = ⟨c :: L, List.replicate k c ++ R⟩ from rfl]
      rw [ih]
      simp only [List.replicate_succ', List.append_assoc, List.singleton_append]

/-- 走完 `padLeft` 写下的预留空白段：头落在 `padStr T` 之后的第一个符号上
    （即区域头格的首个编码符号），左带补上整段 `padStr T`。
    Walking across the pad written by `padLeft`: the head lands on the first symbol
    after the pad and the pad moves to the left tape. -/
theorem moveRightN_padStr (T : Nat) (L : List Sym) (R : List Sym) :
    moveRightN (3 * (T + 1)) ⟨L, padStr T ++ R⟩ = ⟨padStr T ++ L, R⟩ :=
  moveRightN_replicate (3 * (T + 1)) L (some false) R


/-- 右移与迭代可交换：`moveRightN k` 与单步 `moveRight` 复合顺序无关。
    `moveRightN k` commutes with a single right move. -/
theorem moveRightN_move (k : Nat) (t : Tape) :
    moveRightN k (Tape.moveRight t) = Tape.moveRight (moveRightN k t) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
      show moveRightN k (Tape.moveRight (Tape.moveRight t))
        = Tape.moveRight (moveRightN k (Tape.moveRight t))
      rw [ih (Tape.moveRight t)]

/-- 步数可加：`moveRightN (a+b) t = moveRightN b (moveRightN a t)`（先走 `a` 步、再走 `b` 步）。
    Step counts add up: walk `a` steps first, then `b` steps. -/
theorem moveRightN_add (a b : Nat) (t : Tape) :
    moveRightN (a + b) t = moveRightN b (moveRightN a t) := by
  induction b generalizing t with
  | zero => rfl
  | succ b ih =>
      show moveRightN ((a + b) + 1) t = moveRightN (b + 1) (moveRightN a t)
      rw [show moveRightN ((a + b) + 1) t = moveRightN (a + b) (Tape.moveRight t) from rfl]
      rw [show moveRightN (b + 1) (moveRightN a t)
            = moveRightN b (Tape.moveRight (moveRightN a t)) from rfl]
      rw [← show moveRightN a (Tape.moveRight t) = Tape.moveRight (moveRightN a t)
            from moveRightN_move a t]
      rw [ih]

/-- 走完 `padLeft` 的预留段后再右移 2 格：头落在区域头标记 `some true` 上，
    左带补出 `codeSnd`/`codeFst` 与本段 `padStr T`。
    Cross the pad of `padLeft`, then two more cells: the head reaches the region's
    head marker and the left tape gains `codeSnd`/`codeFst` plus the pad. -/
theorem moveRightN_padStr_shift (T : Nat) (a : Sym) (L R : List Sym) :
    moveRightN (2 + 3 * (T + 1)) ⟨L, padStr T ++ codeFst a :: codeSnd a :: some true :: R⟩
      = ⟨codeSnd a :: codeFst a :: (padStr T ++ L), some true :: R⟩ := by
  rw [show 2 + 3 * (T + 1) = 3 * (T + 1) + 2 from by omega]
  rw [moveRightN_add (3 * (T + 1)) 2]
  rw [moveRightN_padStr]
  rfl


/-- 格序列编码的第一格可拆出（头格的格编码 + 其余）。 -/
theorem codeCells_cons (p : Sym × Bool) (ps : List (Sym × Bool)) :
    codeCells (p :: ps) = cellCode p ++ codeCells ps := by
  simp only [codeCells, List.flatMap_cons]

/-- `Reg.initReg` 右侧格列表的显式形态（去掉首格、尾部预留 `kr` 个空白格）。 -/
theorem initReg_post_eq {q : Nat} (st : Fin q) (w : List Bool) (kl kr : Nat) :
    (Reg.initReg st w kl kr).post =
      ((w.map some).drop 1).map (fun s => (s, false)) ++
        List.replicate kr ((none : Sym), false) := rfl

/-- `Reg.initReg` 右侧的格编码串：其余输入格的编码 ++ `3*kr` 个 `some false`。
    这是 `writeRegion` 要写到区域头标记右侧的内容。 -/
theorem codeCells_initReg_post {q : Nat} (st : Fin q) (w : List Bool) (kl kr : Nat) :
    codeCells (Reg.initReg st w kl kr).post =
      codeCells (((w.map some).drop 1).map (fun s => (s, false))) ++
        List.replicate (3 * kr) (some false) := by
  rw [initReg_post_eq, codeCells_append, codeCells_replicate_none]


/-- 全同符号串补尾与补头等价：`replicate n a ++ [a] = a :: replicate n a`。 -/
theorem replicate_snoc_cons (n : Nat) (a : Sym) :
    List.replicate n a ++ [a] = a :: List.replicate n a := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, ih]

/-- 全同符号串（`replicate`）的逆序等于自身。 -/
theorem reverse_replicate_self : ∀ (n : Nat) (a : Sym),
    (List.replicate n a).reverse = List.replicate n a
  | 0, _ => rfl
  | n + 1, a => by
      rw [List.replicate_succ, List.reverse_cons, reverse_replicate_self n a]
      exact replicate_snoc_cons n a

/-- 预留空白段 `padStr` 的逆序等于自身。 -/
theorem reverse_padStr (T : Nat) : (padStr T).reverse = padStr T :=
  reverse_replicate_self (3 * (T + 1)) (some false)

/-- `padLeft` 的输出右移 `2 + 3(T+1)` 步后，**恰好**是初始区域的编码 `Reg.enc`。
    After shifting right by `2 + 3(T+1)`, the output of `padLeft` is exactly
    the padded initial region encoding. -/
theorem padLeft_shift_eq_enc {q : Nat} (st : Fin q) (a : Sym) (T : Nat) (L : List Sym)
    (post : List (Sym × Bool)) :
    moveRightN (2 + 3 * (T + 1))
      ⟨L, padStr T ++ codeFst a :: codeSnd a :: some true :: codeCells post⟩ =
      Reg.enc { state := st, pre := List.replicate (T + 1) ((none : Sym), false), cur := a, post := post } L := by
  rw [moveRightN_padStr_shift]
  simp only [Reg.enc, codeCells_replicate_none_padStr, reverse_padStr]


/-- 预留空白段长度：`padStr T` 有 `3(T+1)` 个符号（= `T+1` 个空白格）。 -/
theorem padStr_length (T : Nat) : (padStr T).length = 3 * (T + 1) := by
  simp [padStr]

/-- 展开步数恒为正（每块至少 1 步）。 -/
theorem expandCost_pos : ∀ (l : List Sym), 0 < expandCost l
  | [] => by simp [expandCost]
  | [_] => by simp [expandCost]
  | a :: b :: rest => by
      have h : expandCost (a :: b :: rest)
          = 2 * (b :: rest).length + 9 + expandCost (b :: rest) := rfl
      omega


/-- 预留空白段 `padStr` 的每个符号都非空白（都是 `some false`）。 -/
theorem padStr_ne_none (T : Nat) : ∀ x ∈ padStr T, x ≠ none := by
  intro x hx
  simp only [padStr, List.mem_replicate] at hx
  obtain ⟨-, rfl⟩ := hx
  simp


/-- 预留空白段 `padStr` 非空（至少一格）。 -/
theorem padStr_ne_nil (T : Nat) : padStr T ≠ [] := by
  simp [padStr]


/-- 格编码的标记位显式形态（拷贝机「标记位 = true」存储用）。 -/
theorem cellCode_marker (a : Sym) (m : Bool) :
    cellCode (a, m) = symCode a ++ [if m then some true else some false] := rfl

/-- 标记位为 1 的格编码：`symCode a` 后接 `some true`（已读副本的存储形态）。 -/
theorem cellCode_true (a : Sym) : cellCode (a, true) = symCode a ++ [some true] := by
  rw [cellCode_marker, if_pos rfl]


/-- 标记位为 0 的格编码：`symCode a` 后接 `some false`（区域正文格的存储形态）。 -/
theorem cellCode_false (a : Sym) : cellCode (a, false) = symCode a ++ [some false] := by
  rw [cellCode_marker, if_neg (by decide)]


/-- 单符号编码非空（`symCode a` 恰两格），供「读格」类论证排除空读。 -/
theorem symCode_ne_nil (a : Sym) : symCode a ≠ [] := by
  cases a with
  | none => simp [symCode]
  | some b => cases b <;> simp [symCode]



/-! ### 左移定位件（区域回读、左向写格用；`moveRightN` 的镜像） -/

/-- 连续左移 `k` 次（与 `moveRightN` 对称的零依赖迭代）。
    Move left `k` times; the mirror of `moveRightN`. -/
def moveLeftN : Nat → Tape → Tape
  | 0, t => t
  | k + 1, t => moveLeftN k (Tape.moveLeft t)

/-- 左带前缀 `l` 上连续左移 `k` 次（`k ≤ l.length`）：前缀的前 `k` 个符号逆序压进右带。
    Moving left `k` times over the prefix `l`: its first `k` symbols, reversed, enter the right tape. -/
theorem moveLeftN_append (k : Nat) (l L R : List Sym) (hk : k ≤ l.length) :
    moveLeftN k ⟨l ++ L, R⟩ = ⟨l.drop k ++ L, (l.take k).reverse ++ R⟩ := by
  induction k generalizing l R with
  | zero => rfl
  | succ k ih =>
      cases l with
      | nil => simp at hk
      | cons a ls =>
          rw [show moveLeftN (k + 1) ⟨(a :: ls) ++ L, R⟩
                = moveLeftN k (Tape.moveLeft ⟨(a :: ls) ++ L, R⟩) from rfl]
          rw [show Tape.moveLeft ⟨(a :: ls) ++ L, R⟩ = ⟨ls ++ L, a :: R⟩ from rfl]
          rw [ih ls (a :: R) (by simp only [List.length_cons] at hk; omega)]
          simp only [List.take_succ_cons, List.drop_succ_cons, List.reverse_cons,
            List.append_assoc, List.singleton_append]

/-- 走完 `padLeft` 写下的预留空白段后原路左移回来：头回到段前，右带补回整段 `padStr T`。
    Walking back over the pad restores the head position and the pad on the right tape. -/
theorem moveLeftN_padStr (T : Nat) (L R : List Sym) :
    moveLeftN (3 * (T + 1)) ⟨padStr T ++ L, R⟩ = ⟨L, padStr T ++ R⟩ := by
  rw [moveLeftN_append _ _ _ _ (by simp [padStr_length])]
  rw [show (padStr T).drop (3 * (T + 1)) = [] from by
        rw [← padStr_length T, List.drop_length]]
  rw [show (padStr T).take (3 * (T + 1)) = padStr T from by
        rw [← padStr_length T, List.take_length]]
  rw [reverse_padStr]
  rfl

/-- 左移与迭代可交换：`moveLeftN k` 与单步 `moveLeft` 复合顺序无关。
    `moveLeftN k` commutes with a single left move. -/
theorem moveLeftN_move (k : Nat) (t : Tape) :
    moveLeftN k (Tape.moveLeft t) = Tape.moveLeft (moveLeftN k t) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
      show moveLeftN k (Tape.moveLeft (Tape.moveLeft t))
        = Tape.moveLeft (moveLeftN k (Tape.moveLeft t))
      rw [ih (Tape.moveLeft t)]

/-- 步数可加：`moveLeftN (a+b) t = moveLeftN b (moveLeftN a t)`。
    Step counts add up for left moves. -/
theorem moveLeftN_add (a b : Nat) (t : Tape) :
    moveLeftN (a + b) t = moveLeftN b (moveLeftN a t) := by
  induction b generalizing t with
  | zero => rfl
  | succ b ih =>
      show moveLeftN ((a + b) + 1) t = moveLeftN (b + 1) (moveLeftN a t)
      rw [show moveLeftN ((a + b) + 1) t = moveLeftN (a + b) (Tape.moveLeft t) from rfl]
      rw [show moveLeftN (b + 1) (moveLeftN a t)
            = moveLeftN b (Tape.moveLeft (moveLeftN a t)) from rfl]
      rw [← show moveLeftN a (Tape.moveLeft t) = Tape.moveLeft (moveLeftN a t)
            from moveLeftN_move a t]
      rw [ih]


end DTM

end Pnp
