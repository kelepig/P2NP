/-
  文件：Pnp/Machine/ExpandInit.lean
  File: Pnp/Machine/ExpandInit.lean

  主题：**区域 ⇒ `Reg.initReg`**——把 `PadRegion` 的右半整链接到初始区域 `Reg.initReg`
        上：左副垫由调用方预先布置在左上下文 `padStr T ++ L` 中，右侧副垫由
        `padStr_run` 写出，于是整条链的终态就是 `Reg.enc (initReg …)`。
  Topic: from the region-assembly chain to `Reg.initReg`. The left pad is supplied by the
  caller as part of the left context (`padStr T ++ L`); the right pad is written by
  `padStr_run`, so the final state is exactly `Reg.enc (Reg.initReg …)`.

  本文件给出：
    - `initReg_enc_eq`：`Reg.initReg` 的 `Reg.enc` 与显式纸带形态的等式；
    - **`expand_pad_to_initReg`**：输入块 ⇒ `Reg.enc (Reg.initReg st w (T+1) (T+1))` 的整链
      （右侧保留尾部 `none :: R`）。
  This file gives the `initReg` encoding equality and the full assembly chain.
-/

import Pnp.Machine.PadRegion

namespace Pnp

namespace DTM

/-- 输入单词的符号编码不含空白（供 `expand` 的非空白前提）。
    The symbol encoding of an input word contains no blank (the expander's hypothesis). -/
theorem map_some_ne_none (w : List Bool) : ∀ v ∈ w.map some, v ≠ none := by
  intro v hv
  simp only [List.mem_map] at hv
  obtain ⟨b, -, rfl⟩ := hv
  simp

/-- **初始区域的编码形态**：`Reg.initReg st w (T+1) (T+1)` 的 `Reg.enc` 恰为
    首格两符号编码 + 左副垫 + `L`、头标记 + 输入余格编码 + 右副垫。
    The explicit tape form of `Reg.initReg`'s encoding. -/
theorem initReg_enc_eq {q : Nat} (st : Fin q) (w : List Bool) (a : Sym) (l' : List Sym)
    (hw : w.map some = a :: l') (T : Nat) (L : List Sym) :
    Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L
      = Tape.mk (codeSnd a :: codeFst a :: (padStr T ++ L))
          (some true :: (codeCells (l'.map (fun s => (s, false))) ++ padStr T)) := by
  rw [enc_initReg_eq_padStr, padStr_reverse, hw]
  simp only [List.headD_cons, List.drop_succ_cons, List.drop_zero, padStr, List.reverse_replicate]

/-- **空前缀形态 ⇒ `initReg` 的编码**：把左副垫放进左上下文后，两种写法给出同一纸带。
    Empty-prefix encoding with the left pad in the context equals the `initReg` encoding. -/
theorem enc_empty_pre_eq_initReg {q : Nat} (st : Fin q) (w : List Bool) (a : Sym)
    (l' : List Sym) (hw : w.map some = a :: l') (T : Nat) (L : List Sym) :
    Reg.enc (⟨st, [], a, l'.map (fun s => (s, false)) ++
        List.replicate (T + 1) ((none : Sym), false)⟩ : Reg q) (padStr T ++ L)
      = Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L := by
  rw [initReg_enc_eq st w a l' hw T L, enc_flat, codeCells_append,
    codeCells_replicate_none_padStr]
  simp only [codeCells, List.flatMap_nil, List.reverse_nil, List.nil_append]

/-- **输入块 ⇒ `Reg.initReg`** 的整链：展开块 `a :: l'`（左上下文已带左副垫
    `padStr T`）、写右副垫、左移 `3(T+1) + 3|l'| + 1` 步、写头标记，终态即
    `Reg.enc (Reg.initReg st w (T+1) (T+1)) L` 的左右分量（右侧保留尾部 `none :: R`）。
    The full chain from an input block to `Reg.enc (Reg.initReg …)`. -/
theorem expand_pad_to_initReg {q : Nat} (st : Fin q) (w : List Bool) (a : Sym) (l' : List Sym)
    (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none) (T : Nat) (L R : List Sym) :
    markHead.run 1
      ⟨markHead.start,
        Tape.moveLeft
          (moveLeftN (3 * l'.length)
            (moveLeftN (3 * (T + 1))
              ((writeStr (padStr T)).run (3 * (T + 1))
                ⟨(writeStr (padStr T)).start,
                  (expand.run (expandCost (a :: l'))
                    ⟨(⟨0, by omega⟩ : Fin 128),
                      Tape.mk (padStr T ++ L) (((a :: l') ++
                          List.replicate (2 * (a :: l').length + 1) none) ++
                        (List.replicate (3 * (T + 1)) none ++ R))⟩).tape⟩).tape))⟩
      = ⟨markHead.accept,
          Tape.mk ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).left)
            ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).right ++ none :: R)⟩ := by
  -- 目标右侧换成「空前缀 + 左副垫在上下文里」的写法
  rw [← enc_empty_pre_eq_initReg st w a l' hw T L]
  -- 整链
  rw [expand_pad_to_enc st a l' hl T (padStr T ++ L) R]

/-- **输入块 ⇒ `Reg.initReg st w m m`（副垫长度参数化）**：与 `expand_pad_to_initReg` 同链，
    只把右（和左）副垫的空白格数从 `T+1` 换成任意 `m ≥ 1`；代换 `T := m - 1`。
    The same assembly chain with the pad size `m` (instead of `T+1`) as a parameter. -/
theorem expand_pad_to_initReg_pad {q : Nat} (st : Fin q) (w : List Bool) (a : Sym)
    (l' : List Sym) (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none)
    (m : Nat) (hm : 1 ≤ m) (L R : List Sym) :
    markHead.run 1
      ⟨markHead.start,
        Tape.moveLeft
          (moveLeftN (3 * l'.length)
            (moveLeftN (3 * m)
              ((writeStr (padStr (m - 1))).run (3 * m)
                ⟨(writeStr (padStr (m - 1))).start,
                  (expand.run (expandCost (a :: l'))
                    ⟨(⟨0, by omega⟩ : Fin 128),
                      Tape.mk (padStr (m - 1) ++ L) (((a :: l') ++
                          List.replicate (2 * (a :: l').length + 1) none) ++
                        (List.replicate (3 * m) none ++ R))⟩).tape⟩).tape))⟩
      = ⟨markHead.accept,
          Tape.mk ((Reg.enc (Reg.initReg st w m m) L).left)
            ((Reg.enc (Reg.initReg st w m m) L).right ++ none :: R)⟩ := by
  -- 代换 `T := m - 1`，并把 `(m-1)+1`、`3*((m-1)+1)` 归约回 `m`、`3*m`
  have hs : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have h := expand_pad_to_initReg st w a l' hw hl (m - 1) L R
  rw [hs] at h
  exact h


end DTM

end Pnp
