/-
  文件：Pnp/Machine/AlignChain.lean
  File: Pnp/Machine/AlignChain.lean

  主题：E 机的**区域装配段**——把「展开 → 写右副垫 → 左移定位 → 写头标记」拼成一台机器。
  Topic: the region-assembly segment of E as a single machine, i.e. expand, write the right
  padding, scan left and write the head marker.

  机器形态：`alignChain pad n := seqComp expand (seqComp (writeStr pad) (markAlign n))`，
  其中 `pad` 是副垫串、`n` 是左移格数。本文给出
    - `padAlign_run` / `padAlign_halted_false`：内层组合（写串 + 定位写标记）的整段运行与不停机；
    - `alignChain_run`：整台机器的运行规格（终点纸带 = 左移 `n` 格后写 `some true`）。
  The machine is a two-level `seqComp`; the file proves the inner composition's run and
  non-halting, then the whole machine's exact run.
-/

import Pnp.Machine.ExpandNoHalt
import Pnp.Machine.ExpandInit
import Pnp.Machine.WriteBack
import Pnp.Machine.GoComp
import Pnp.Machine.RightPad

namespace Pnp

namespace DTM

/-- **`writeStr` 在自己步数内不停机**（终止态唯一，状态值 = 已写符号数）。
    `writeStr` never halts before writing all its symbols. -/
theorem writeStr_halted_false (l : List Sym) (k : Nat) (L R : List Sym) (hk : k < l.length) :
    (writeStr l).halted ((writeStr l).run k ⟨(writeStr l).start, Tape.mk L R⟩) = false := by
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

/-- **`markAlign` 走完左移段**：`n+1` 步后落在右段起点（`markHead` 的起始态）。
    After `n+1` steps `markAlign` sits at `markHead`'s start state. -/
theorem markAlign_pre (n : Nat) (t : Tape) (hr : t.right ≠ []) :
    (markAlign n).run (n + 1) ⟨(markAlign n).start, t⟩
      = ⟨Fin.natAdd (n + 1) markHead.start, moveLeftN n t⟩ := by
  have hne : (moveLeftN n t).right ≠ [] := moveLeftN_right_ne_of_pos n t hr
  have hnhA : ∀ i, i < n → (goLeft n).halted ((goLeft n).run i ⟨(goLeft n).start, t⟩) = false := by
    intro i hi
    rw [show (goLeft n).start = (⟨0, by omega⟩ : Fin (n + 1)) from rfl]
    rw [goLeft_run_from n i 0 t (by omega) hr]
    exact goLeft_halted_false n (0 + i) (by omega) (moveLeftN i t)
  have hrun_a : (markAlign n).run n ⟨(markAlign n).start, t⟩
      = ⟨Fin.castAdd 2 ((goLeft n).run n ⟨(goLeft n).start, t⟩).state,
         ((goLeft n).run n ⟨(goLeft n).start, t⟩).tape⟩ := by
    change (seqComp (goLeft n) markHead).run n _ = _
    exact seqComp_embed_left (goLeft n) markHead n ⟨(goLeft n).start, t⟩ hnhA
  have hstep : (markAlign n).run 1
      ⟨Fin.castAdd 2 ((goLeft n).run n ⟨(goLeft n).start, t⟩).state,
       ((goLeft n).run n ⟨(goLeft n).start, t⟩).tape⟩
      = ⟨Fin.natAdd (n + 1) markHead.start, moveLeftN n t⟩ := by
    change (seqComp (goLeft n) markHead).run 1 _ = _
    rw [goLeft_run n t hr]
    have hsw := seqComp_switch (goLeft n) markHead
      ⟨(⟨n, by omega⟩ : Fin (n + 1)), moveLeftN n t⟩ rfl
    rw [hsw]
    rw [show ((moveLeftN n t).write (moveLeftN n t).read).move Dir.stay = moveLeftN n t from by
      rw [Tape.write_read _ hne, Tape.move]]
  rw [DTM.run_add (markAlign n) n 1 ⟨(markAlign n).start, t⟩, hrun_a]
  exact hstep

/-- **`markAlign` 的状态进度**：前 `n+2` 步内第 `j` 步的状态值恰为 `j`。
    State progress of `markAlign`: after `j ≤ n+2` steps the state value is exactly `j`. -/
theorem markAlign_state_val (n : Nat) (t : Tape) (hr : t.right ≠ []) (j : Nat)
    (hj : j ≤ n + 1 + 1) :
    ((markAlign n).run j ⟨(markAlign n).start, t⟩).state.val = j := by
  rcases Nat.lt_or_ge j (n + 1) with hj1 | hj1
  · -- 左移段
    have hnhA : ∀ i, i < j →
        (goLeft n).halted ((goLeft n).run i ⟨(goLeft n).start, t⟩) = false := by
      intro i hi
      rw [show (goLeft n).start = (⟨0, by omega⟩ : Fin (n + 1)) from rfl]
      rw [goLeft_run_from n i 0 t (by omega) hr]
      exact goLeft_halted_false n (0 + i) (by omega) (moveLeftN i t)
    have hrun : (markAlign n).run j ⟨(markAlign n).start, t⟩
        = ⟨Fin.castAdd 2 ((goLeft n).run j ⟨(goLeft n).start, t⟩).state,
           ((goLeft n).run j ⟨(goLeft n).start, t⟩).tape⟩ := by
      change (seqComp (goLeft n) markHead).run j _ = _
      exact seqComp_embed_left (goLeft n) markHead j ⟨(goLeft n).start, t⟩ hnhA
    rw [hrun]
    have hg : (goLeft n).run j ⟨(goLeft n).start, t⟩
        = ⟨(⟨0 + j, by omega⟩ : Fin (n + 1)), moveLeftN j t⟩ := by
      rw [show (goLeft n).start = (⟨0, by omega⟩ : Fin (n + 1)) from rfl]
      exact goLeft_run_from n j 0 t (by omega) hr
    rw [hg]
    simp
  · rcases Nat.eq_or_lt_of_le hj1 with heq | hlt
    · -- 第 `n+1` 步：右段起点
      subst heq
      rw [markAlign_pre n t hr]
      simp [markHead]
    · -- 第 `n+2` 步：接受态
      have hj2 : j = n + 1 + 1 := by omega
      subst hj2
      rw [markAlign_run n t hr]
      have hacc : (markAlign n).accept.val = n + 1 + 1 := by
        show (Fin.natAdd (n + 1) markHead.accept).val = n + 1 + 1
        rw [Fin.val_natAdd]
        rfl
      rw [hacc]

/-- **`markAlign` 走满前不停机**（`j < n+2`）。
    `markAlign` never halts during its `n+2` steps. -/
theorem markAlign_halted_false (n : Nat) (t : Tape) (hr : t.right ≠ []) (j : Nat)
    (hj : j < n + 1 + 1) :
    (markAlign n).halted ((markAlign n).run j ⟨(markAlign n).start, t⟩) = false := by
  have hval := markAlign_state_val n t hr j (by omega)
  have hacc : (markAlign n).accept.val = n + 1 + 1 := by
    show (Fin.natAdd (n + 1) markHead.accept).val = n + 1 + 1
    rw [Fin.val_natAdd]
    rfl
  have hrej : (markAlign n).reject.val = n + 1 + 1 := by
    show (Fin.natAdd (n + 1) markHead.reject).val = n + 1 + 1
    rw [Fin.val_natAdd]
    rfl
  refine halted_false_of_ne (markAlign n) _ ?_ ?_
  · intro h
    have hv := congrArg Fin.val h
    rw [hval, hacc] at hv
    omega
  · intro h
    have hv := congrArg Fin.val h
    rw [hval, hrej] at hv
    omega

/-- 空白副垫的 `drop`：`none :: none^k ++ X` 去掉前 `k` 格恰剩 `none :: X`。
    Dropping the reserved blanks leaves exactly one blank before the tail. -/
theorem drop_cons_replicate (k : Nat) (X : List Sym) :
    ((none :: (List.replicate k none ++ X)).drop k) = none :: X := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [show List.replicate (k + 1) none = none :: List.replicate k none from rfl,
        List.cons_append]
      exact ih

/-- **内层组合**：写副垫 `pad` 后接「左移 `n` 格 + 写头标记」。
    The inner composition: write the padding `pad`, then locate and mark the head. -/
def alignInner (pad : List Sym) (n : Nat) : DTM ((pad.length + 1) + ((n + 1) + 2)) :=
  seqComp (writeStr pad) (markAlign n)

/-- **内层组合的整段运行**：`|pad| + 1 + (n + 2)` 步后纸带左移 `n` 格并把头格写 `some true`。
    Full run of the inner composition. -/
theorem padAlign_run (pad : List Sym) (n : Nat) (L0 R0 : List Sym)
    (hne : (R0.drop pad.length) ≠ []) :
    (alignInner pad n).run (pad.length + 1 + (n + 1 + 1))
      ⟨(alignInner pad n).start, Tape.mk L0 R0⟩
      = ⟨(alignInner pad n).accept,
          (moveLeftN n (Tape.mk (pad.reverse ++ L0) (R0.drop pad.length))).write (some true)⟩ := by
  refine seqComp_run (writeStr pad) (markAlign n) pad.length (n + 1 + 1)
    ⟨(writeStr pad).start, Tape.mk L0 R0⟩
    (Tape.mk (pad.reverse ++ L0) (R0.drop pad.length))
    ((moveLeftN n (Tape.mk (pad.reverse ++ L0) (R0.drop pad.length))).write (some true))
    (writeStr_run pad L0 R0) hne ?_ ?_ ?_
  · exact markAlign_run n _ hne
  · intro k hk
    exact writeStr_halted_false pad k L0 R0 hk
  · intro k hk
    exact markAlign_halted_false n _ hne k hk

/-- **内层组合在自己的步数内不停机**。
    The inner composition never halts during its own steps. -/
theorem padAlign_halted_false (pad : List Sym) (n : Nat) (L0 R0 : List Sym)
    (hne : (R0.drop pad.length) ≠ []) (k : Nat)
    (hk : k < pad.length + 1 + (n + 1 + 1)) :
    (alignInner pad n).halted ((alignInner pad n).run k
      ⟨(alignInner pad n).start, Tape.mk L0 R0⟩) = false := by
  have hnhW : ∀ i, i < pad.length →
      (writeStr pad).halted ((writeStr pad).run i ⟨(writeStr pad).start, Tape.mk L0 R0⟩)
        = false := fun i hi => writeStr_halted_false pad i L0 R0 hi
  -- 左段（含切换前的最后一个格局）的停机否定
  have hleft : ∀ k, k ≤ pad.length → (alignInner pad n).halted
      ((alignInner pad n).run k ⟨(alignInner pad n).start, Tape.mk L0 R0⟩) = false := by
    intro k hk'
    have hrun : (alignInner pad n).run k ⟨(alignInner pad n).start, Tape.mk L0 R0⟩
        = ⟨Fin.castAdd ((n + 1) + 2)
            ((writeStr pad).run k ⟨(writeStr pad).start, Tape.mk L0 R0⟩).state,
           ((writeStr pad).run k ⟨(writeStr pad).start, Tape.mk L0 R0⟩).tape⟩ := by
      change (seqComp (writeStr pad) (markAlign n)).run k _ = _
      exact seqComp_embed_left (writeStr pad) (markAlign n) k
        ⟨(writeStr pad).start, Tape.mk L0 R0⟩ (fun i hi => hnhW i (by omega))
    rw [hrun]
    have h1 := (seqComp_halt_castAdd (writeStr pad) (markAlign n)
      ((writeStr pad).run k ⟨(writeStr pad).start, Tape.mk L0 R0⟩).state).1.symm
    have h2 := (seqComp_halt_castAdd (writeStr pad) (markAlign n)
      ((writeStr pad).run k ⟨(writeStr pad).start, Tape.mk L0 R0⟩).state).2.symm
    exact halted_false_of_ne _ _ h1 h2
  rcases Nat.lt_or_ge k (pad.length + 1) with hk1 | hk1
  · -- 左段
    exact hleft k (by omega)
  · -- `k ≥ |pad| + 1`：切换后进入右段
    obtain ⟨j, hj⟩ : ∃ j, k = (pad.length + 1) + j :=
      ⟨k - (pad.length + 1), by omega⟩
    subst hj
    -- 前 `|pad|+1` 步：写串 + 切换
    have hpre : (alignInner pad n).run (pad.length + 1)
        ⟨(alignInner pad n).start, Tape.mk L0 R0⟩
        = ⟨Fin.natAdd (pad.length + 1) (markAlign n).start,
            Tape.mk (pad.reverse ++ L0) (R0.drop pad.length)⟩ := by
      rw [DTM.run_add (alignInner pad n) pad.length 1,
        show (alignInner pad n).run pad.length ⟨(alignInner pad n).start, Tape.mk L0 R0⟩
          = ⟨Fin.castAdd ((n + 1) + 2)
              ((writeStr pad).run pad.length
                ⟨(writeStr pad).start, Tape.mk L0 R0⟩).state,
             ((writeStr pad).run pad.length
                ⟨(writeStr pad).start, Tape.mk L0 R0⟩).tape⟩ from by
          change (seqComp (writeStr pad) (markAlign n)).run pad.length _ = _
          exact seqComp_embed_left (writeStr pad) (markAlign n) pad.length
            ⟨(writeStr pad).start, Tape.mk L0 R0⟩ (fun i hi => hnhW i hi),
        writeStr_run pad L0 R0]
      change (seqComp (writeStr pad) (markAlign n)).run 1 _ = _
      have hsw := seqComp_switch (writeStr pad) (markAlign n)
        ⟨(writeStr pad).accept, Tape.mk (pad.reverse ++ L0) (R0.drop pad.length)⟩ rfl
      rw [hsw]
      rw [show ((Tape.mk (pad.reverse ++ L0) (R0.drop pad.length)).write
          (Tape.mk (pad.reverse ++ L0) (R0.drop pad.length)).read).move Dir.stay
          = Tape.mk (pad.reverse ++ L0) (R0.drop pad.length) from by
        rw [Tape.write_read _ hne, Tape.move]]
    -- 右段：`markAlign` 的 `j` 步
    have hnhB : ∀ i, i < j → (markAlign n).halted ((markAlign n).run i
        ⟨(markAlign n).start, Tape.mk (pad.reverse ++ L0) (R0.drop pad.length)⟩)
        = false := fun i hi => markAlign_halted_false n _ hne i (by omega)
    rw [DTM.run_add (alignInner pad n) (pad.length + 1) j, hpre,
      show (alignInner pad n).run j
        ⟨Fin.natAdd (pad.length + 1) (markAlign n).start,
          Tape.mk (pad.reverse ++ L0) (R0.drop pad.length)⟩
        = ⟨Fin.natAdd (pad.length + 1) ((markAlign n).run j
            ⟨(markAlign n).start, Tape.mk (pad.reverse ++ L0) (R0.drop pad.length)⟩).state,
           ((markAlign n).run j
            ⟨(markAlign n).start, Tape.mk (pad.reverse ++ L0) (R0.drop pad.length)⟩).tape⟩
        from by
          change (seqComp (writeStr pad) (markAlign n)).run j _ = _
          exact seqComp_embed_right (writeStr pad) (markAlign n) j _ hnhB]
    -- 右段状态值 = `j < n+2`，故不是终止态
    have hval := markAlign_state_val n
      (Tape.mk (pad.reverse ++ L0) (R0.drop pad.length)) hne j (by omega)
    have hacc : (markAlign n).accept.val = n + 1 + 1 := by
      show (Fin.natAdd (n + 1) markHead.accept).val = n + 1 + 1
      rw [Fin.val_natAdd]
      rfl
    have hrej : (markAlign n).reject.val = n + 1 + 1 := by
      show (Fin.natAdd (n + 1) markHead.reject).val = n + 1 + 1
      rw [Fin.val_natAdd]
      rfl
    have hne1 : ((markAlign n).run j
        ⟨(markAlign n).start, Tape.mk (pad.reverse ++ L0) (R0.drop pad.length)⟩).state
        ≠ (markAlign n).accept := by
      intro h
      have hv := congrArg Fin.val h
      rw [hval, hacc] at hv
      omega
    have hne2 : ((markAlign n).run j
        ⟨(markAlign n).start, Tape.mk (pad.reverse ++ L0) (R0.drop pad.length)⟩).state
        ≠ (markAlign n).reject := by
      intro h
      have hv := congrArg Fin.val h
      rw [hval, hrej] at hv
      omega
    have h1 := (seqComp_halt_natAdd (writeStr pad) (markAlign n) _ hne1 hne2).1.symm
    have h2 := (seqComp_halt_natAdd (writeStr pad) (markAlign n) _ hne1 hne2).2.symm
    exact halted_false_of_ne _ _ h1 h2

/-- **整台装配机**：展开 → 写副垫 → 左移 `n` 格 → 写头标记。
    The whole assembly machine. -/
def alignChain (pad : List Sym) (n : Nat) :
    DTM (128 + ((pad.length + 1) + ((n + 1) + 2))) :=
  seqComp expand (alignInner pad n)

/-- **装配机的整段运行**：输入块 ⇒ 左移 `n` 格并写头标记的纸带。
    Full run of the assembly machine. -/
theorem alignChain_run (pad : List Sym) (n : Nat) (l' : List Sym)
    (hl : ∀ v ∈ l', v ≠ none) (M R : List Sym) :
    (alignChain pad n).run (expandCost l' + 1 + (pad.length + 1 + (n + 1 + 1)))
      ⟨(alignChain pad n).start,
        Tape.mk M (l' ++ List.replicate (2 * l'.length + 1) none
          ++ (List.replicate pad.length none ++ R))⟩
      = ⟨(alignChain pad n).accept,
          (moveLeftN n (Tape.mk (pad.reverse ++ (codesRev l' ++ M))
            (none :: R))).write (some true)⟩ := by
  have hdrop : ((none :: (List.replicate pad.length none ++ R)).drop pad.length)
      = none :: R := drop_cons_replicate pad.length R
  refine seqComp_run expand (alignInner pad n) (expandCost l')
    (pad.length + 1 + (n + 1 + 1))
    ⟨(⟨0, by omega⟩ : Fin 128),
      Tape.mk M (l' ++ List.replicate (2 * l'.length + 1) none
        ++ (List.replicate pad.length none ++ R))⟩
    (Tape.mk (codesRev l' ++ M) (none :: (List.replicate pad.length none ++ R)))
    ((moveLeftN n (Tape.mk (pad.reverse ++ (codesRev l' ++ M))
      (none :: R))).write (some true))
    (expand_run l' hl M _) (by simp) ?_ ?_ ?_
  · have h := padAlign_run pad n (codesRev l' ++ M)
      (none :: (List.replicate pad.length none ++ R)) (by rw [hdrop]; simp)
    rw [hdrop] at h
    exact h
  · intro k hk
    exact expand_halted_false l' hl M _ k hk
  · intro k hk
    exact padAlign_halted_false pad n (codesRev l' ++ M)
      (none :: (List.replicate pad.length none ++ R)) (by rw [hdrop]; simp) k hk

/-- 右带非空的纸带可写成「头符号 + 余下」形态。
    A tape with a nonempty right side splits as head symbol plus remainder. -/
theorem tape_exists_cons (t : Tape) (h : t.right ≠ []) :
    ∃ L a R, t = Tape.mk L (a :: R) := by
  obtain ⟨Lm, R, ht0⟩ : ∃ Lm R, t = Tape.mk Lm R := ⟨_, _, rfl⟩
  have hR : R ≠ [] := by
    intro hnil
    exact h (by rw [ht0, hnil])
  cases R with
  | nil => exact absurd rfl hR
  | cons a as => exact ⟨Lm, a, as, ht0⟩

/-- `markHead` 一步的「写标记」形态（与 `markHead_run` 的展开式等价）。
    One step of `markHead` seen as writing `some true` in place. -/
theorem markHead_write (t : Tape) (h : t.right ≠ []) :
    markHead.run 1 ⟨markHead.start, t⟩ = ⟨markHead.accept, t.write (some true)⟩ := by
  obtain ⟨L, a, R, ht⟩ := tape_exists_cons t h
  rw [ht]
  exact markHead_run L a R

/-- **装配机 ⇒ `Reg.initReg` 的区域编码**：输入块展开、写右副垫、左移 `3(T+1)+3|l'|+1` 格
    并写头标记后，纸带恰是 `Reg.enc (Reg.initReg …)` 的左右分量（右侧多一个空白）。
    这是 `ExpandInit.expand_pad_to_initReg` 的**机器级**版本。
    Machine-level form of `expand_pad_to_initReg`: one machine produces the initial region. -/
theorem alignChain_to_initReg {q : Nat} (st : Fin q) (w : List Bool) (a : Sym) (l' : List Sym)
    (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none) (T : Nat) (L R : List Sym) :
    (alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1)).run
      (expandCost (a :: l') + 1
        + ((padStr T).length + 1 + (3 * (T + 1) + 3 * l'.length + 1 + 1 + 1)))
      ⟨(alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1)).start,
        Tape.mk (padStr T ++ L) ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
          ++ (List.replicate (padStr T).length none ++ R))⟩
      = ⟨(alignChain (padStr T) (3 * (T + 1) + 3 * l'.length + 1)).accept,
          Tape.mk ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).left)
            ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).right ++ none :: R)⟩ := by
  -- 左端：整台机器的运行规格
  have hrun := alignChain_run (padStr T) (3 * (T + 1) + 3 * l'.length + 1) (a :: l')
    hl (padStr T ++ L) R
  rw [hrun]
  -- 副垫写串后的显式纸带
  have hwrite : ((writeStr (padStr T)).run (3 * (T + 1))
      ⟨(writeStr (padStr T)).start,
        Tape.mk (codesRev (a :: l') ++ (padStr T ++ L))
          (none :: (List.replicate (3 * (T + 1)) none ++ R))⟩).tape
      = Tape.mk ((padStr T).reverse ++ (codesRev (a :: l') ++ (padStr T ++ L))) (none :: R) := by
    rw [padStr_reverse]
    exact congrArg Config.tape
      (padStr_run' T (codesRev (a :: l') ++ (padStr T ++ L)) R)
  -- 参考运行：分段写法，终点同为目标纸带
  have hexp := expand_pad_to_initReg st w a l' hw hl T L R
  rw [show (expand.run (expandCost (a :: l'))
        ⟨(⟨0, by omega⟩ : Fin 128),
          Tape.mk (padStr T ++ L) (((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none) ++
            (List.replicate (3 * (T + 1)) none ++ R))⟩).tape
      = Tape.mk (codesRev (a :: l') ++ (padStr T ++ L))
          (none :: (List.replicate (3 * (T + 1)) none ++ R)) from
      congrArg Config.tape (expand_run (a :: l') hl (padStr T ++ L)
        (List.replicate (3 * (T + 1)) none ++ R))] at hexp
  rw [hwrite] at hexp
  rw [markHead_write _ (Tape.moveLeft_right_ne _)] at hexp
  -- 两种左移写法给出同一纸带，再引用参考运行的终点
  rw [show moveLeftN (3 * (T + 1) + 3 * l'.length + 1)
        (Tape.mk ((padStr T).reverse ++ (codesRev (a :: l') ++ (padStr T ++ L))) (none :: R))
      = Tape.moveLeft (moveLeftN (3 * l'.length) (moveLeftN (3 * (T + 1))
          (Tape.mk ((padStr T).reverse ++ (codesRev (a :: l') ++ (padStr T ++ L))) (none :: R)))) from by
    rw [show 3 * (T + 1) + 3 * l'.length + 1 = 3 * (T + 1) + (3 * l'.length + 1) from by omega]
    rw [moveLeftN_split3]]
  have htape : (moveLeftN (3 * l'.length) (moveLeftN (3 * (T + 1))
      (Tape.mk ((padStr T).reverse ++ (codesRev (a :: l') ++ (padStr T ++ L)))
        (none :: R)))).moveLeft.write (some true)
      = Tape.mk ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).left)
          ((Reg.enc (Reg.initReg st w (T + 1) (T + 1)) L).right ++ none :: R) :=
    congrArg Config.tape hexp
  rw [htape]

/-- **装配机 ⇒ `Reg.initReg st w m m`（副垫参数化）**：与 `alignChain_to_initReg` 同链，
    副垫空白格数取任意 `m ≥ 1`；代换 `T := m - 1`。
    Machine-level assembly with a free pad size `m` (`T := m - 1`). -/
theorem alignChain_to_initReg_pad {q : Nat} (st : Fin q) (w : List Bool) (a : Sym)
    (l' : List Sym) (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none)
    (m : Nat) (hm : 1 ≤ m) (L R : List Sym) :
    (alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1)).run
      (expandCost (a :: l') + 1
        + ((padStr (m - 1)).length + 1 + (3 * m + 3 * l'.length + 1 + 1 + 1)))
      ⟨(alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1)).start,
        Tape.mk (padStr (m - 1) ++ L) ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
          ++ (List.replicate (padStr (m - 1)).length none ++ R))⟩
      = ⟨(alignChain (padStr (m - 1)) (3 * m + 3 * l'.length + 1)).accept,
          Tape.mk ((Reg.enc (Reg.initReg st w m m) L).left)
            ((Reg.enc (Reg.initReg st w m m) L).right ++ none :: R)⟩ := by
  have hs : m - 1 + 1 = m := Nat.sub_add_cancel hm
  have h := alignChain_to_initReg st w a l' hw hl (m - 1) L R
  rw [hs] at h
  exact h


/-- **区域装配整机在自己的步数内不停机**（`seqComp_no_halt` 的整机版，供相位串接使用）。
    The whole region-assembly machine never halts before its final step. -/
theorem alignChain_halted_false (pad : List Sym) (n : Nat) (l' : List Sym)
    (hl : ∀ v ∈ l', v ≠ none) (M R : List Sym) (k : Nat)
    (hk : k < expandCost l' + 1 + (pad.length + 1 + (n + 1 + 1))) :
    (alignChain pad n).halted ((alignChain pad n).run k
      ⟨(alignChain pad n).start,
        Tape.mk M (l' ++ List.replicate (2 * l'.length + 1) none
          ++ (List.replicate pad.length none ++ R))⟩) = false := by
  have hdrop : ((none :: (List.replicate pad.length none ++ R)).drop pad.length) = none :: R :=
    drop_cons_replicate pad.length R
  refine seqComp_no_halt expand (alignInner pad n) (expandCost l') _ _ _
    (expand_run l' hl M _) (by simp) ?_ ?_ k hk
  · intro j hj
    exact expand_halted_false l' hl M _ j hj
  · intro j hj
    exact padAlign_halted_false pad n (codesRev l' ++ M)
      (none :: (List.replicate pad.length none ++ R)) (by rw [hdrop]; simp) j hj

/-- **装配段终点 = 理想区域编码 + 右侧远尾**：`alignChain_to_initReg` 的终态纸带只是理想
    初始区域编码在右端多挂了一段空白尾，正是右尾绝缘（`Tape.PadRight`）的接口形态。
    The endpoint is the ideal region encoding with a far-right tail: the `PadRight` interface. -/
theorem enc_padRight_append {q : Nat} (x : Reg q) (L R : List Sym) :
    Tape.PadRight (Reg.enc x L)
      (Tape.mk (Reg.enc x L).left ((Reg.enc x L).right ++ none :: R)) :=
  ⟨rfl, none :: R, rfl⟩

end DTM

end Pnp
