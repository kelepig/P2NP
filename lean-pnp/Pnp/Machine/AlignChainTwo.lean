/-
  文件：Pnp/Machine/AlignChainTwo.lean
  File: Pnp/Machine/AlignChainTwo.lean

  主题：**左右副垫解耦**的机器级区域装配——左垫 `padStr (Pl-1)` 来自初始纸带上下文，
        右垫 `padStr T` 由装配段写出，终态为 `Reg.enc (Reg.initReg st w Pl (T+1))`。
  Topic: machine-level assembly with decoupled pads.

  用途（B5 缺陷修复 #265）：把左垫固定、只放大右垫，使机器层右预留前提可满足。
  Purpose: fixes the vacuous right-pad premise (#265) by decoupling the two pads.
-/

import Pnp.Machine.ExpandInitTwo
import Pnp.Machine.AlignChain

namespace Pnp

namespace DTM

/-- **装配机 ⇒ 解耦初始区域 `Reg.initReg st w Pl (T+1)`**：左垫 `padStr (Pl-1)` 只出现在初始
    纸带上下文，右垫 `padStr T` 由装配段写出；终态是区域编码左右分量（右侧多一个空白）。
    Machine-level assembly with decoupled pads: the left pad stays in the context and the
    right pad is written, yielding the encoding of `Reg.initReg st w Pl (T+1)`. -/
theorem alignChain_to_initReg_two {q : Nat} (st : Fin q) (w : List Bool) (a : Sym) (l' : List Sym)
    (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none) (Pl T : Nat) (hPl : 1 ≤ Pl) (L R : List Sym) :
    (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1)).run
      (expandCost (a :: l') + 1
        + ((padStr T).length + 1 + (3 * (T + 1) + 3 * l'.length + 1 + 1 + 1)))
      ⟨(alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1)).start,
        Tape.mk (padStr (Pl - 1) ++ L) ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
          ++ (List.replicate (padStr T).length none ++ R))⟩
      = ⟨(alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1)).accept,
          Tape.mk ((Reg.enc (Reg.initReg st w Pl (T + 1)) L).left)
            ((Reg.enc (Reg.initReg st w Pl (T + 1)) L).right ++ none :: R)⟩ := by
  -- 左端：整台机器的运行规格
  have hrun := alignChain_run (padStr T) (3 * (T + 1) + 3 * l'.length + 1) (a :: l')
    hl (padStr (Pl - 1) ++ L) R
  rw [hrun]
  -- 副垫写串后的显式纸带
  have hwrite : ((writeStr (padStr T)).run (3 * (T + 1))
      ⟨(writeStr (padStr T)).start,
        Tape.mk (codesRev (a :: l') ++ (padStr (Pl - 1) ++ L))
          (none :: (List.replicate (3 * (T + 1)) none ++ R))⟩).tape
      = Tape.mk ((padStr T).reverse ++ (codesRev (a :: l') ++ (padStr (Pl - 1) ++ L))) (none :: R) := by
    rw [padStr_reverse]
    exact congrArg Config.tape
      (padStr_run' T (codesRev (a :: l') ++ (padStr (Pl - 1) ++ L)) R)
  -- 参考运行：分段写法，终点同为目标纸带
  have hexp := expand_pad_to_initReg_two st w a l' hw hl Pl (T + 1) hPl (by omega) L R
  -- 参考运行的右垫是 `padStr ((T+1)-1)`，先归约成 `padStr T`
  rw [show (T + 1) - 1 = T from by omega] at hexp
  rw [show (expand.run (expandCost (a :: l'))
        ⟨(⟨0, by omega⟩ : Fin 128),
          Tape.mk (padStr (Pl - 1) ++ L) (((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none) ++
            (List.replicate (3 * (T + 1)) none ++ R))⟩).tape
      = Tape.mk (codesRev (a :: l') ++ (padStr (Pl - 1) ++ L))
          (none :: (List.replicate (3 * (T + 1)) none ++ R)) from
      congrArg Config.tape (expand_run (a :: l') hl (padStr (Pl - 1) ++ L)
        (List.replicate (3 * (T + 1)) none ++ R))] at hexp
  rw [hwrite] at hexp
  rw [markHead_write _ (Tape.moveLeft_right_ne _)] at hexp
  -- 两种左移写法给出同一纸带，再引用参考运行的终点
  rw [show moveLeftN (3 * (T + 1) + 3 * l'.length + 1)
        (Tape.mk ((padStr T).reverse ++ (codesRev (a :: l') ++ (padStr (Pl - 1) ++ L))) (none :: R))
      = Tape.moveLeft (moveLeftN (3 * l'.length) (moveLeftN (3 * (T + 1))
          (Tape.mk ((padStr T).reverse ++ (codesRev (a :: l') ++ (padStr (Pl - 1) ++ L))) (none :: R)))) from by
    rw [show 3 * (T + 1) + 3 * l'.length + 1 = 3 * (T + 1) + (3 * l'.length + 1) from by omega]
    rw [moveLeftN_split3]]
  have htape : (moveLeftN (3 * l'.length) (moveLeftN (3 * (T + 1))
      (Tape.mk ((padStr T).reverse ++ (codesRev (a :: l') ++ (padStr (Pl - 1) ++ L)))
        (none :: R)))).moveLeft.write (some true)
      = Tape.mk ((Reg.enc (Reg.initReg st w Pl (T + 1)) L).left)
          ((Reg.enc (Reg.initReg st w Pl (T + 1)) L).right ++ none :: R) :=
    congrArg Config.tape hexp
  rw [htape]


end DTM

end Pnp
