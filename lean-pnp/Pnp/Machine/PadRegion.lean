/-
  文件：Pnp/Machine/PadRegion.lean
  File: Pnp/Machine/PadRegion.lean

  主题：**区域右侧预留段**——展开输入块后，在区域右侧写入 `padStr T`（`3(T+1)` 个
        空白符号编码），再把读写头搬回首格标记并写头标记；整链得到「前缀为空、
        后缀带 `T+1` 个空白格」的 `Reg.enc` 形态。
  Topic: the region's right pad. After expanding the input block, write `padStr T` to the
  right of the region, walk the head back to the first cell's marker, and write the marker.

  本文件给出：
    - `cons_replicate` / `drop_replicate`：重复段与 `cons` 的交换、以及丢弃；
    - `padStr_run`：写入机把 `padStr T` 写进 `3(T+1)` 个空白格的确切运行；
    - **`expand_pad_to_enc`**：展开 + 右副垫 + 回位 + 写标记的整链（纸带级），
      结论按 `Reg.enc`（前缀空、后缀 `l' ++ T+1 空白格`）的左右分量给出。
  This file gives the right-pad run and the full expand-pad-rewind-mark chain.
-/

import Pnp.Machine.ExpandEnc
import Pnp.Machine.WriteStr
import Pnp.Machine.WritePadL
import Pnp.Machine.PadLeft

namespace Pnp

namespace DTM

/-- 格局的纸带投影（字面量构造时即取第二分量，供 `simp` 消去 `.tape`）。
    The tape projection of a literal configuration. -/
@[simp] theorem config_tape_mk {q : Nat} (s : Fin q) (t : Tape) :
    ((⟨s, t⟩ : Config q)).tape = t := rfl

/-! ### 重复段的两个初等恒等式 -/

/-- `c :: (replicate k c ++ R) = replicate k c ++ (c :: R)`：`cons` 穿过重复段。
    A `cons` commutes with a repetition block. -/
theorem cons_replicate (k : Nat) (c : Sym) (R : List Sym) :
    c :: (List.replicate k c ++ R) = List.replicate k c ++ (c :: R) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simp only [List.replicate_succ, List.cons_append]
      rw [ih]

/-- `(replicate k c ++ R).drop k = R`：丢弃整段重复。
    Dropping a whole repetition block. -/
theorem drop_replicate (k : Nat) (c : Sym) (R : List Sym) :
    (List.replicate k c ++ R).drop k = R := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append,
        show (c :: (List.replicate k c ++ R)).drop (k + 1)
          = (List.replicate k c ++ R).drop k from rfl]
      exact ih

/-! ### 右副垫的写入 -/

/-- 副垫真垫的丢弃：消费 `(padStr T).length` 个空白后剩 `none :: R`。
    Dropping the pad's blanks. -/
theorem padStr_drop (T : Nat) (R : List Sym) :
    (List.replicate (3 * (T + 1)) none ++ (none :: R)).drop (padStr T).length = none :: R := by
  rw [padStr_length]
  exact drop_replicate _ none (none :: R)

/-- **写右副垫**：在 `3(T+1)` 个空白格（其后再接 `R`）上写 `padStr T`，左侧得到
    `padStr T ++ L`，读写头停在副垫右侧一格。
    Writing the right pad over `3(T+1)` blanks. -/
theorem padStr_run (T : Nat) (L R : List Sym) :
    (writeStr (padStr T)).run (padStr T).length
      ⟨(writeStr (padStr T)).start,
        Tape.mk L (none :: List.replicate (3 * (T + 1)) none ++ R)⟩
      = ⟨(writeStr (padStr T)).accept, Tape.mk (padStr T ++ L) (none :: R)⟩ := by
  -- 把「多出的一个空白」并入重复段
  rw [show none :: List.replicate (3 * (T + 1)) none ++ R
        = List.replicate (3 * (T + 1)) none ++ (none :: R) from cons_replicate _ none R]
  -- 写入机主引理
  rw [writeStr_run (padStr T) L (List.replicate (3 * (T + 1)) none ++ (none :: R))]
  rw [padStr_drop]
  rw [padStr_reverse]

/-- 步数写成 `3(T+1)` 的版本（供复合链直接引用）。
    The `3(T+1)`-step form, for use in the composite chain. -/
theorem padStr_run' (T : Nat) (L R : List Sym) :
    (writeStr (padStr T)).run (3 * (T + 1))
      ⟨(writeStr (padStr T)).start,
        Tape.mk L (none :: List.replicate (3 * (T + 1)) none ++ R)⟩
      = ⟨(writeStr (padStr T)).accept, Tape.mk (padStr T ++ L) (none :: R)⟩ := by
  simpa only [padStr_length] using padStr_run T L R

/-! ### 展开 ⇒ 带右副垫的区域编码 -/

set_option maxHeartbeats 1000000 in
/-- **展开 + 写右副垫**（两段）：展开块 `a :: l'`（后接 `2|l'|+1` 个展开空白、
    `3(T+1)` 个副垫空白、再是 `R`），再在这些副垫空白上写 `padStr T`。
    Expand the block, then write the right pad over the reserved blanks. -/
theorem expand_pad_tape (a : Sym) (l' : List Sym) (hl : ∀ v ∈ a :: l', v ≠ none)
    (T : Nat) (M R : List Sym) :
    ((writeStr (padStr T)).run (3 * (T + 1))
      ⟨(writeStr (padStr T)).start,
        (expand.run (expandCost (a :: l'))
          ⟨(⟨0, by omega⟩ : Fin 128),
            Tape.mk M (((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none) ++
              (List.replicate (3 * (T + 1)) none ++ R))⟩).tape⟩).tape
      = Tape.mk (padStr T ++ ((codeCells ((a :: l').map (fun s => (s, false)))).reverse ++ M))
          (none :: R) := by
  -- ① 展开：把内层纸带换成扁平形态
  have h1 : (expand.run (expandCost (a :: l'))
      ⟨(⟨0, by omega⟩ : Fin 128),
        Tape.mk M (((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none) ++
          (List.replicate (3 * (T + 1)) none ++ R))⟩).tape
      = Tape.mk ((codeCells ((a :: l').map (fun s => (s, false)))).reverse ++ M)
          (none :: (List.replicate (3 * (T + 1)) none ++ R)) :=
    congrArg (fun c => c.tape)
      (expand_flat a l' hl M (List.replicate (3 * (T + 1)) none ++ R))
  rw [h1]
  -- ② 写右副垫
  exact congrArg (fun c => c.tape)
    (padStr_run' T ((codeCells ((a :: l').map (fun s => (s, false)))).reverse ++ M) R)

/-- **带副垫的扁平形态 ⇒ `Reg.enc`**：跨过副垫、`post` 格编码，回位并写头标记。
    From the padded flat form back to `Reg.enc` (prefix empty, suffix padded). -/
theorem pad_tape_to_enc {q : Nat} (st : Fin q) (a : Sym) (l' : List Sym) (T : Nat)
    (M R : List Sym) :
    markHead.run 1
      ⟨markHead.start,
        Tape.moveLeft
          (moveLeftN (3 * l'.length)
            (moveLeftN (3 * (T + 1))
              ⟨padStr T ++ ((codeCells ((a :: l').map (fun s => (s, false)))).reverse ++ M),
                none :: R⟩))⟩
      = ⟨markHead.accept,
          Tape.mk ((Reg.enc (⟨st, [], a, l'.map (fun s => (s, false)) ++
                List.replicate (T + 1) ((none : Sym), false)⟩ : Reg q) M).left)
            ((Reg.enc (⟨st, [], a, l'.map (fun s => (s, false)) ++
                List.replicate (T + 1) ((none : Sym), false)⟩ : Reg q) M).right ++
              none :: R)⟩ := by
  -- ③ 左移跨过副垫
  rw [moveLeftN_padStr T ((codeCells ((a :: l').map (fun s => (s, false)))).reverse ++ M)
    (none :: R)]
  -- ④ 跨过 `post` 的格编码：拆出首格
  rw [show ((a :: l').map (fun s => (s, false)))
        = (a, false) :: l'.map (fun s => (s, false)) from rfl]
  rw [show ((a, false) :: l'.map (fun s => (s, false)))
        = ([] : List (Sym × Bool)) ++ [(a, false)] ++ l'.map (fun s => (s, false)) from rfl]
  rw [codeCells_split_reverse, append_cellRev_cons]
  rw [show (cellMark (a, false).snd :: codeSnd (a, false).fst :: codeFst (a, false).fst :: M)
        = (some false :: codeSnd a :: codeFst a :: M) from rfl]
  rw [show 3 * l'.length = 3 * (l'.map (fun s => (s, false))).length from by
        rw [List.length_map]]
  rw [moveLeftN_codeCells (l'.map (fun s => (s, false)))
    (some false :: codeSnd a :: codeFst a :: M) (padStr T ++ none :: R)]
  -- ⑤ 再左移一格并写头标记
  rw [show Tape.moveLeft ⟨some false :: (codeSnd a :: codeFst a :: M),
        codeCells (l'.map (fun s => (s, false))) ++ (padStr T ++ none :: R)⟩
      = ⟨codeSnd a :: codeFst a :: M,
        some false :: (codeCells (l'.map (fun s => (s, false))) ++ (padStr T ++ none :: R))⟩
      from rfl]
  rw [markHead_run (codeSnd a :: codeFst a :: M) (some false)
    (codeCells (l'.map (fun s => (s, false))) ++ (padStr T ++ none :: R))]
  -- ⑥ 对齐到 `Reg.enc` 的左右分量
  rw [show (Reg.enc (⟨st, [], a, l'.map (fun s => (s, false)) ++
          List.replicate (T + 1) ((none : Sym), false)⟩ : Reg q) M).left
        = codeSnd a :: codeFst a :: M from by
      rw [enc_flat]
      simp only [codeCells, List.flatMap_nil, List.reverse_nil, List.nil_append]]
  rw [show (Reg.enc (⟨st, [], a, l'.map (fun s => (s, false)) ++
          List.replicate (T + 1) ((none : Sym), false)⟩ : Reg q) M).right
        = some true :: (codeCells (l'.map (fun s => (s, false))) ++ padStr T) from by
      rw [enc_flat, codeCells_append]
      rw [show codeCells (List.replicate (T + 1) ((none : Sym), false)) = padStr T from
        codeCells_replicate_none_padStr T]]
  simp only [List.cons_append, List.append_assoc]

/-- **展开 + 右副垫 + 回位 + 写标记**（整链）：得到 `Reg.enc ⟨st, [], a, l' ++ T+1 空白格⟩`
    的形态，右侧保留尾部 `none :: R`。
    The full chain from the expanded block to the encoded region. -/
theorem expand_pad_to_enc {q : Nat} (st : Fin q) (a : Sym) (l' : List Sym)
    (hl : ∀ v ∈ a :: l', v ≠ none) (T : Nat) (M R : List Sym) :
    markHead.run 1
      ⟨markHead.start,
        Tape.moveLeft
          (moveLeftN (3 * l'.length)
            (moveLeftN (3 * (T + 1))
              ((writeStr (padStr T)).run (3 * (T + 1))
                ⟨(writeStr (padStr T)).start,
                  (expand.run (expandCost (a :: l'))
                    ⟨(⟨0, by omega⟩ : Fin 128),
                      Tape.mk M (((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none) ++
                        (List.replicate (3 * (T + 1)) none ++ R))⟩).tape⟩).tape))⟩
      = ⟨markHead.accept,
          Tape.mk ((Reg.enc (⟨st, [], a, l'.map (fun s => (s, false)) ++
                List.replicate (T + 1) ((none : Sym), false)⟩ : Reg q) M).left)
            ((Reg.enc (⟨st, [], a, l'.map (fun s => (s, false)) ++
                List.replicate (T + 1) ((none : Sym), false)⟩ : Reg q) M).right ++
              none :: R)⟩ := by
  rw [expand_pad_tape a l' hl T M R]
  exact pad_tape_to_enc st a l' T M R

end DTM

end Pnp
