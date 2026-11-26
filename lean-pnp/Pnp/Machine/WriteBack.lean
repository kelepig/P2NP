/-
  文件：Pnp/Machine/WriteBack.lean
  File: Pnp/Machine/WriteBack.lean

  主题：**写串 + 归位**——在当前位置写入常量串 `l`，随后用走位机把读写头搬回原格。
        这是区域装配（`writeRegion` / `restoreRegion`）里反复出现的「写一段再回原位」腿：
        `writeBack l = seqComp (writeStr l) (goLeft l.length)`。
  Topic: write a constant string at the head and walk the head back to where it started.
  `writeBack l = seqComp (writeStr l) (goLeft l.length)`; a leg used repeatedly by the
  region-assembly machines.

  本文件给出：
    - `writeStr_run_state_val`：`writeStr` 前 `m` 步（`m ≤ |l|`）后状态值恰为 `m`；
    - `writeBack`：两台机器的顺序组合；
    - `writeBack_run`：整段运行后的确切纸带 `Tape.mk L (l ++ R.drop |l|)`。
  This file gives the state-progress lemma for the writer, the composite machine, and its
  exact run shape.
-/

import Pnp.Machine.WriteStr
import Pnp.Machine.SeqComp
import Pnp.Machine.Go

namespace Pnp

namespace DTM

/-- `writeStr` 前 `m` 步（`m ≤ |l|`）之后，状态值恰好是 `m`。
    After `m ≤ |l|` steps the writer's state value is exactly `m`. -/
theorem writeStr_run_state_val (l : List Sym) :
    ∀ (m : Nat) (L R : List Sym), m ≤ l.length →
      ((writeStr l).run m ⟨(writeStr l).start, Tape.mk L R⟩).state.val = m := by
  induction l with
  | nil =>
      intro m L R hm
      have hm0 : m = 0 := by simpa using hm
      subst hm0
      rfl
  | cons b l' ih =>
      intro m L R hm
      cases m with
      | zero => rfl
      | succ k =>
          -- 起始状态不是终止态（0 ≠ |l'|+1）
          have hne : (writeStr (b :: l')).start ≠ (writeStr (b :: l')).accept := by
            intro h
            have hv := congrArg Fin.val h
            simp [writeStr] at hv
          have hrej : (writeStr (b :: l')).reject = (writeStr (b :: l')).accept := rfl
          have hnh : (writeStr (b :: l')).halted
              ⟨(writeStr (b :: l')).start, Tape.mk L R⟩ = false := by
            simp [DTM.halted, hne, hrej]
          rw [DTM.run_succ_of_not_halted _ k _ hnh]
          -- 第一步：写下 `b` 并右移，进入 `l'` 机（状态上移一格）
          have h1 : (writeStr (b :: l')).stepConfig
              ⟨(writeStr (b :: l')).start, Tape.mk L R⟩
              = ⟨Fin.succ (writeStr l').start, Tape.mk (b :: L) R.tail⟩ := by
            simp only [DTM.stepConfig, writeStr, writeStrStep, Tape.read, Tape.write,
              Tape.move, Tape.moveRight]
            rfl
          rw [h1]
          -- 后续 `k` 步由状态上移的搬运引理交回 `l'` 机
          rw [show (writeStr (b :: l')).run k ⟨Fin.succ (writeStr l').start,
                Tape.mk (b :: L) R.tail⟩
              = ⟨Fin.succ ((writeStr l').run k ⟨(writeStr l').start,
                    Tape.mk (b :: L) R.tail⟩).state,
                  ((writeStr l').run k ⟨(writeStr l').start,
                    Tape.mk (b :: L) R.tail⟩).tape⟩
            from writeStr_run_succ b l' k ⟨(writeStr l').start, Tape.mk (b :: L) R.tail⟩]
          -- 状态值 = 上一层的值 + 1 = k + 1
          rw [Fin.val_succ]
          rw [ih k (b :: L) R.tail (by simpa using hm)]

/-- **写串后归位机**：先写 `l`，再由左走位机把头搬回段首。
    Writer followed by a left walk back to the start of the written region. -/
abbrev writeBack (l : List Sym) : DTM ((l.length + 1) + (l.length + 1)) :=
  seqComp (writeStr l) (goLeft l.length)

/-- **写串 + 归位的整段运行**：在当前位置写入 `l`，头搬回原格；纸带右侧变为
    `l ++ R.drop |l|`（被写入区覆盖）。需右侧至少有 `|l| + 1` 个符号。
    Exact run of the write-and-return machine: writing `l` at the head and walking back
    leaves `Tape.mk L (l ++ R.drop |l|)`; requires `|l| < |R|`. -/
theorem writeBack_run (l : List Sym) (L R : List Sym) (hR : l.length < R.length) :
    (writeBack l).run (l.length + 1 + l.length)
      ⟨(writeBack l).start, Tape.mk L R⟩
      = ⟨(writeBack l).accept, Tape.mk L (l ++ R.drop l.length)⟩ := by
  -- 右侧在被写入区之后仍非空（供「读符号原样写回」与走位引理使用）
  have hne : R.drop l.length ≠ [] := by
    intro h
    rw [List.drop_eq_nil_iff] at h
    omega
  -- 第一段：写串（前缀内不停机）
  have hnh₁ : ∀ k, k < l.length →
      (writeStr l).halted ((writeStr l).run k ⟨(writeStr l).start, Tape.mk L R⟩) = false := by
    intro k hk
    have hval := writeStr_run_state_val l k L R (by omega)
    have hacc : (writeStr l).accept.val = l.length := rfl
    have hrejv : (writeStr l).reject.val = l.length := rfl
    refine halted_false_of_ne (writeStr l)
      ((writeStr l).run k ⟨(writeStr l).start, Tape.mk L R⟩) ?_ ?_
    · intro h
      have hv := congrArg Fin.val h
      simp only [hval, hacc] at hv
      omega
    · intro h
      have hv := congrArg Fin.val h
      simp only [hval, hrejv] at hv
      omega
  -- 第二段：左走位（中间状态均不在终止态）
  have hnh₂ : ∀ k, k < l.length →
      (goLeft l.length).halted ((goLeft l.length).run k
        ⟨(goLeft l.length).start, Tape.mk (l.reverse ++ L) (R.drop l.length)⟩) = false := by
    intro k hk
    have hrun : (goLeft l.length).run k
        ⟨(goLeft l.length).start, Tape.mk (l.reverse ++ L) (R.drop l.length)⟩
        = ⟨(⟨k, by omega⟩ : Fin (l.length + 1)),
            moveLeftN k (Tape.mk (l.reverse ++ L) (R.drop l.length))⟩ := by
      simpa only [goLeft, Nat.zero_add] using
        (goLeft_run_from l.length k 0 (Tape.mk (l.reverse ++ L) (R.drop l.length))
          (by omega) hne)
    rw [hrun]
    exact goLeft_halted_false l.length k hk _
  -- 第一段搬运：组合机前 `|l|` 步 = 写串的整段运行
  have hstep1 : (writeBack l).run l.length ⟨(writeBack l).start, Tape.mk L R⟩
      = ⟨Fin.castAdd (l.length + 1) (writeStr l).accept,
          Tape.mk (l.reverse ++ L) (R.drop l.length)⟩ := by
    have h := seqComp_embed_left (writeStr l) (goLeft l.length) l.length
      ⟨(writeStr l).start, Tape.mk L R⟩ hnh₁
    rw [writeStr_run l L R] at h
    simpa only [writeBack, seqComp] using h
  -- 步数拆成两段
  rw [show l.length + 1 + l.length = l.length + (1 + l.length) from by omega]
  rw [DTM.run_add (writeBack l) l.length (1 + l.length), hstep1]
  -- 第二段拆成「切换 1 步 + 左走位 |l| 步」
  rw [DTM.run_add (writeBack l) 1 l.length]
  have hsw : (writeBack l).run 1
      ⟨Fin.castAdd (l.length + 1) (writeStr l).accept,
        Tape.mk (l.reverse ++ L) (R.drop l.length)⟩
      = ⟨Fin.natAdd (l.length + 1) (goLeft l.length).start,
          Tape.mk (l.reverse ++ L) (R.drop l.length)⟩ := by
    have h := seqComp_switch (writeStr l) (goLeft l.length)
      ⟨(writeStr l).accept, Tape.mk (l.reverse ++ L) (R.drop l.length)⟩ rfl
    rw [show ((Tape.mk (l.reverse ++ L) (R.drop l.length)).write
                (Tape.mk (l.reverse ++ L) (R.drop l.length)).read).move Dir.stay
              = Tape.mk (l.reverse ++ L) (R.drop l.length) from by
          rw [Tape.write_read _ hne, Tape.move]] at h
    simpa only [writeBack, seqComp] using h
  rw [hsw]
  -- 第二段搬运：组合机后 `|l|` 步 = 左走位机的整段运行
  have hstep2 : (writeBack l).run l.length
      ⟨Fin.natAdd (l.length + 1) (goLeft l.length).start,
        Tape.mk (l.reverse ++ L) (R.drop l.length)⟩
      = ⟨Fin.natAdd (l.length + 1) (⟨l.length, Nat.lt_succ_self l.length⟩ : Fin (l.length + 1)),
          moveLeftN l.length (Tape.mk (l.reverse ++ L) (R.drop l.length))⟩ := by
    have h := seqComp_embed_right (writeStr l) (goLeft l.length) l.length
      ⟨(goLeft l.length).start, Tape.mk (l.reverse ++ L) (R.drop l.length)⟩ hnh₂
    rw [goLeft_run l.length _ hne] at h
    simpa only [writeBack, seqComp] using h
  rw [hstep2]
  -- 左移穿过写入区：左侧回到 `L`，右侧补回写入串
  rw [show moveLeftN l.length ⟨l.reverse ++ L, R.drop l.length⟩
        = ⟨L, l ++ R.drop l.length⟩ from by
      rw [moveLeftN_append l.length l.reverse L (R.drop l.length) (by simp)]
      rw [show (l.reverse).drop l.length = [] from by
            rw [← List.length_reverse, List.drop_length]]
      rw [show (l.reverse).take l.length = l.reverse from by
            rw [← List.length_reverse, List.take_length]]
      simp]
  -- 终态：组合机的接受态恰是左走位机的接受态（同一状态值 `|l|`）
  rfl

end DTM

end Pnp
