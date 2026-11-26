/-
  文件：Pnp/Machine/ExpandInitTwo.lean
  File: Pnp/Machine/ExpandInitTwo.lean

  主题：**左右副垫解耦**的区域装配——左垫 `padStr (Pl-1)` 只作上下文，
        右垫 `padStr Pr` 由装配段写出，产出 `Reg.enc (Reg.initReg st w Pl Pr)`。
  Topic: region assembly with decoupled pads — the left pad stays in the tape context,
  the right pad is written, yielding `Reg.enc (Reg.initReg st w Pl Pr)`.

  用途（B5 缺陷修复 #265）：机器层右预留前提要求「右长 ≥ 预算」，而预算随左垫增大；
  把左垫固定为 `T+1`、只放大右垫 `Pr`，前提即可满足。
  Purpose: keeps the left pad fixed at `T+1` and grows only the right pad, so the
  right-length premise of the machine-level theorems becomes satisfiable.
-/

import Pnp.Machine.ExpandInit

namespace Pnp

namespace DTM

/-- 非对称初始区域的编码形态（`rfl`）：左垫 `Pl`、右垫 `Pr` 各自独立。
    Explicit encoding of the asymmetric initial region. -/
theorem enc_initReg_eq_two {q : Nat} (st : Fin q) (w : List Bool) (Pl Pr : Nat)
    (L : List Sym) :
    Reg.enc (Reg.initReg st w Pl Pr) L =
      Tape.mk (codeSnd ((w.map some).headD none) :: codeFst ((w.map some).headD none) ::
          (List.reverse (codeCells (List.replicate Pl ((none : Sym), false))) ++ L))
        (some true :: codeCells ((((w.map some).drop 1).map (fun s => (s, false))) ++
          List.replicate Pr ((none : Sym), false))) := rfl

/-- 用 `padStr` 改写的非对称形态：左垫 `reverse (padStr (Pl-1))`、右垫 `3·Pr` 个空白。
    Same shape with `padStr` on both pads. -/
theorem enc_initReg_eq_padStr_two {q : Nat} (st : Fin q) (w : List Bool) (Pl Pr : Nat)
    (hPl : 1 ≤ Pl) (L : List Sym) :
    Reg.enc (Reg.initReg st w Pl Pr) L =
      Tape.mk (codeSnd ((w.map some).headD none) :: codeFst ((w.map some).headD none) ::
          (List.reverse (padStr (Pl - 1)) ++ L))
        (some true :: (codeCells (((w.map some).drop 1).map (fun s => (s, false)))
          ++ List.replicate (3 * Pr) (some false))) := by
  rw [enc_initReg_eq_two, codeCells_append, codeCells_replicate_none Pr]
  -- 左垫：`Pl` 格编码的反转 = `padStr (Pl-1)`
  have hpre : List.reverse (codeCells (List.replicate Pl ((none : Sym), false)))
      = List.reverse (padStr (Pl - 1)) := by
    rw [codeCells_replicate_none Pl]
    have h3 : 3 * Pl = 3 * ((Pl - 1) + 1) := by omega
    rw [h3]
    simp [padStr]
  rw [hpre]

/-- **空前缀 + 左垫在上下文 ⇒ 非对称 `initReg` 的编码**。
    Empty-prefix encoding with the left pad in the context equals the asymmetric region. -/
theorem enc_empty_pre_eq_initReg_two {q : Nat} (st : Fin q) (w : List Bool) (a : Sym)
    (l' : List Sym) (hw : w.map some = a :: l') (Pl Pr : Nat) (hPl : 1 ≤ Pl) (L : List Sym) :
    Reg.enc (⟨st, [], a, l'.map (fun s => (s, false)) ++
        List.replicate Pr ((none : Sym), false)⟩ : Reg q) (padStr (Pl - 1) ++ L)
      = Reg.enc (Reg.initReg st w Pl Pr) L := by
  rw [enc_initReg_eq_padStr_two st w Pl Pr hPl L, enc_flat, codeCells_append,
    codeCells_replicate_none Pr]
  simp only [codeCells, List.flatMap_nil, List.reverse_nil, List.nil_append]
  rw [padStr_reverse, hw]
  simp only [List.headD_cons, List.drop_succ_cons, List.drop_zero]

/-- **输入块 ⇒ 非对称 `Reg.initReg`（左垫 `Pl`、右垫 `Pr`）** 的整段运行：
    左垫来自初始纸带的左上下文，右垫由写串段写出。
    The assembly run with decoupled pads. -/
theorem expand_pad_to_initReg_two {q : Nat} (st : Fin q) (w : List Bool) (a : Sym)
    (l' : List Sym) (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none)
    (Pl Pr : Nat) (hPl : 1 ≤ Pl) (hPr : 1 ≤ Pr) (L R : List Sym) :
    markHead.run 1
      ⟨markHead.start,
        Tape.moveLeft
          (moveLeftN (3 * l'.length)
            (moveLeftN (3 * Pr)
              ((writeStr (padStr (Pr - 1))).run (3 * Pr)
                ⟨(writeStr (padStr (Pr - 1))).start,
                  (expand.run (expandCost (a :: l'))
                    ⟨(⟨0, by omega⟩ : Fin 128),
                      Tape.mk (padStr (Pl - 1) ++ L) (((a :: l') ++
                          List.replicate (2 * (a :: l').length + 1) none) ++
                        (List.replicate (3 * Pr) none ++ R))⟩).tape⟩).tape))⟩
      = ⟨markHead.accept,
          Tape.mk ((Reg.enc (Reg.initReg st w Pl Pr) L).left)
            ((Reg.enc (Reg.initReg st w Pl Pr) L).right ++ none :: R)⟩ := by
  have hs : Pr - 1 + 1 = Pr := Nat.sub_add_cancel hPr
  rw [← enc_empty_pre_eq_initReg_two st w a l' hw Pl Pr hPl L]
  have h := expand_pad_to_enc st a l' hl (Pr - 1) (padStr (Pl - 1) ++ L) R
  rw [hs] at h
  exact h

end DTM

end Pnp
