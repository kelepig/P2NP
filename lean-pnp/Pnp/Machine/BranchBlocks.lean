/-
  文件：Pnp/Machine/BranchBlocks.lean
  File: Pnp/Machine/BranchBlocks.lean

  主题：分支下标 → 数字块列表的编码（含末位哨兵）。
  Topic: encoding a branch index into digit blocks, with a trailing sentinel block.

  背景（#137/#140）：通路的第 j 块数字决定第 j+1 轮的选号（`passRun` 以 `c := k + 1`
  递归），故块值就是解码位本身，块列表只比选号序列少一项。取
  `branchBlocks = [c₂, …, c_T, B]`、首轮下标 `c₀ = c₁ + 1 = i % B + 1`，则前 `T` 轮
  下标恰为 `(seqOfIndex B T i).map (· + 1)`——正是占位机 `M.stutter` 模拟原机选择
  序列所用的下标；`passEnd` 的计数器为 `B+1`，而 `M.stutter` 候选表长 ≤ `B+1`，
  故多出来的那一轮在相位 4 查表失败，不改变读数。
  Background (#137/#140): block j sets the next choice to `k + 1`, so a block's value
  is the decoded digit itself and the list is one term shorter than the choice
  sequence. With the head index `i % B + 1` the first `T` rounds use exactly the
  stutter indices of the original choices; `passEnd` then carries `B + 1`, beyond every
  `M.stutter` candidate list, so the extra round dies in phase 4.

  本文件给出：
    - `seqHead` / `branchBlocks`（定义）；
    - `seqHead_lt`、`branchBlocks_length`、`branchBlocks_hb`（类型层基本事实）。
  This file defines the head choice and the block list, with their basic facts.
-/

import Pnp.Machine.EnumAssembly
import Pnp.Machine.SimPass
import Pnp.Machine.Stutter

namespace Pnp

/-- 分支 `i` 的**首轮下标**：解码首项 `i % B` 在占位机里要 `+1`（`T = 0` 时不用）。
    首轮用这个下标查表，故需 `≤ B < 2^b`。
    First-round index for branch `i`: the decoded head `i % B` shifted by one, because
    the simulated machine is the stutter machine. -/
def seqHead (B T i : Nat) : Nat := i % B + 1

/-- 分支 `i` 的**数字块列表**：解码序列去掉首项（块 `k` 决定下一轮选号 `k+1`，
    故块值即解码位本身），末尾补哨兵 `B`（其 `+1` 超出一切 `stutter` 候选表，
    使多余一轮查表失败）。配合首轮下标 `seqHead = i % B + 1`，前 `T` 轮的下标恰为
    `(seqOfIndex B T i).map (· + 1)`，即占位机模拟原机选择序列所用的下标。
    Block list for branch `i`: the decoded sequence without its head (a block's value
    is the decoded digit itself), plus a dying sentinel `B`. -/
def branchBlocks (B T i : Nat) : List Nat :=
  (seqOfIndex B T i).drop 1 ++ [B]

/-- 首轮下标在界内：`i % B + 1 ≤ B`（故 `< 2^b`）。The head index is at most `B`. -/
theorem seqHead_lt (B T i : Nat) (hB : 0 < B) : seqHead B T i ≤ B := by
  simp only [seqHead]
  exact Nat.succ_le_of_lt (Nat.mod_lt i hB)

/-- 块列表长度恰为 `T`（`T ≥ 1`）。The block list has exactly `T` entries. -/
theorem branchBlocks_length (B T i : Nat) (hT : 0 < T) :
    (branchBlocks B T i).length = T := by
  simp only [branchBlocks, List.length_append, List.length_drop,
    seqOfIndex_length, List.length_singleton]
  omega

/-- 块列表的界：每块 `k` 都满足 `k + 2 < 2^b`（哨兵 `B` 由 `B + 2 < 2^b` 保证）。 -/
theorem branchBlocks_hb (B T i b : Nat) (hB : 0 < B) (hb : B + 2 < 2 ^ b) :
    ∀ k' ∈ branchBlocks B T i, k' + 2 < 2 ^ b := by
  intro k' hk'
  rcases List.mem_append.mp hk' with hk' | hk'
  · have hmem : k' ∈ seqOfIndex B T i := List.mem_of_mem_drop hk'
    have hcB : k' < B := seqOfIndex_lt_bound B T i hB k' hmem
    omega
  · simp only [List.mem_singleton] at hk'
    subst hk'
    omega

/-- 首轮下标在 `2^b` 以内（`B + 2 < 2^b` 的直接推论），供 `passStart` 的 `hc` 用。
    The head index is below `2^b`, the `hc` argument of `passStart`. -/
theorem seqHead_lt_pow (B T i b : Nat) (hB : 0 < B) (hb : B + 2 < 2 ^ b) :
    seqHead B T i < 2 ^ b := by
  have h1 := seqHead_lt B T i hB
  omega

/-- 块列表长度即 `T`（`T ≥ 1`）时，区域两侧各留 `T + 1` 格空白即满足 `passRun` 的填充前提。
    Padding `T + 1` cells on both sides suffices for the pass padding premises. -/
theorem branchBlocks_pad {B T i : Nat} (hT : 0 < T) {α : Type} (L : List α)
    (hL : T + 1 ≤ L.length) : (branchBlocks B T i).length + 1 ≤ L.length := by
  rw [branchBlocks_length B T i hT]
  exact hL

/-- **解码前缀一致**：先按 `t` 位解码，等于按 `T` 位解码后取前 `t` 位（`t ≤ T`）。
    Prefix consistency of the index decoding. -/
theorem seqOfIndex_take (B : Nat) :
    ∀ (t T i : Nat), t ≤ T → seqOfIndex B t i = (seqOfIndex B T i).take t := by
  intro t
  induction t with
  | zero => intro T i _; rfl
  | succ t ih =>
      intro T i ht
      cases T with
      | zero => omega
      | succ T' =>
          simp only [seqOfIndex, List.take_succ_cons]
          rw [ih T' (i / B) (by omega)]

/-- 分支块列表的「长解码前缀」形式（`t ≤ T`）：
    `branchBlocks B t i = ((seqOfIndex B T i).take t).drop 1 ++ [B]`。
    The `t`-round block list as a prefix of the `T`-digit decoding plus the sentinel. -/
theorem branchBlocks_eq_prefix {B T i t : Nat} (ht : t ≤ T) :
    branchBlocks B t i = ((seqOfIndex B T i).take t).drop 1 ++ [B] := by
  simp only [branchBlocks]
  rw [seqOfIndex_take B t T i ht]

/-- `pick` 越界返回 `none`。`pick` returns `none` past the end of the list. -/
theorem pick_eq_none_of_le {α : Type} :
    ∀ (l : List α) (i : Nat), l.length ≤ i → pick l i = none
  | [], _, _ => rfl
  | _ :: _, 0, h => by simp at h
  | _ :: l, i + 1, h => pick_eq_none_of_le l i (by simpa using h)

namespace DTM

/-- **哨兵定位**：若块列表的末块是 `k` 且通路成功，则终态计数器为 `k + 1`
    （`passRun` 每处理一块就以 `k + 1` 递归，末块的 `+1` 即终态计数器）。
    If the block list ends in `k`, a successful pass ends with counter `k + 1`. -/
theorem passRun_getLast_c (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    ∀ (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q)
      (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) (r : PassRes q b),
      passRun q b tab Z c hc x L hb = some r →
      ∀ (k : Nat), L.getLast? = some k → r.c = k + 1 := by
  intro L
  induction L with
  | nil =>
      intro Z c hc x hb r _ k hk
      simp at hk
  | cons k0 L' ih =>
      intro Z c hc x hb r hpass k hk
      cases hpk : pick (tab x.state x.cur) c with
      | none =>
          rw [passRun_none_unfold q b tab Z c hc x k0 L' hb hpk] at hpass
          cases hpass
      | some v =>
          obtain ⟨m', s', d⟩ := v
          -- 单块（递归到空表）：基例计数器即 `k0 + 1`
          -- 多块：计数器来自归纳假设
          cases L' with
          | nil =>
              have hk0 : k = k0 := by simpa using hk.symm
              rw [hk0]
              cases d with
              | stay =>
                  rw [passRun_stay_unfold q b tab Z c hc x k0 [] hb m' s' hpk] at hpass
                  obtain ⟨r0, hrec, hr⟩ := Option.map_eq_some_iff.mp hpass
                  rw [← hr]
                  have hc0 : r0.c = k0 + 1 := by
                    have h := congrArg (Option.map (fun r : PassRes q b => r.c)) hrec
                    simp only [passRun, Option.map_some] at h
                    exact (Option.some.inj h).symm
                  exact hc0
              | right =>
                  cases hpost : x.post with
                  | nil => simp only [passRun, hpk, hpost] at hpass; cases hpass
                  | cons p post' =>
                      rw [passRun_right_unfold q b tab Z c hc x k0 [] hb m' s' p post'
                        hpost hpk] at hpass
                      obtain ⟨r0, hrec, hr⟩ := Option.map_eq_some_iff.mp hpass
                      rw [← hr]
                      have hc0 : r0.c = k0 + 1 := by
                        have h := congrArg (Option.map (fun r : PassRes q b => r.c)) hrec
                        simp only [passRun, Option.map_some] at h
                        exact (Option.some.inj h).symm
                      exact hc0
              | left =>
                  cases hrev : x.pre.reverse with
                  | nil => simp only [passRun, hpk, hrev] at hpass; cases hpass
                  | cons cq preRev =>
                      rw [passRun_left_unfold q b tab Z c hc x k0 [] hb m' s' cq preRev
                        hrev hpk] at hpass
                      obtain ⟨r0, hrec, hr⟩ := Option.map_eq_some_iff.mp hpass
                      rw [← hr]
                      have hc0 : r0.c = k0 + 1 := by
                        have h := congrArg (Option.map (fun r : PassRes q b => r.c)) hrec
                        simp only [passRun, Option.map_some] at h
                        exact (Option.some.inj h).symm
                      exact hc0
          | cons k1 L'' =>
              have hk' : (k1 :: L'').getLast? = some k := by simpa using hk
              cases d with
              | stay =>
                  rw [passRun_stay_unfold q b tab Z c hc x k0 (k1 :: L'') hb m' s' hpk]
                    at hpass
                  obtain ⟨r0, hrec, hr⟩ := Option.map_eq_some_iff.mp hpass
                  rw [← hr]
                  exact ih (Z + k0 + 3) (k0 + 1) _ _ _ r0 hrec k hk'
              | right =>
                  cases hpost : x.post with
                  | nil => simp only [passRun, hpk, hpost] at hpass; cases hpass
                  | cons p post' =>
                      rw [passRun_right_unfold q b tab Z c hc x k0 (k1 :: L'') hb m' s' p
                        post' hpost hpk] at hpass
                      obtain ⟨r0, hrec, hr⟩ := Option.map_eq_some_iff.mp hpass
                      rw [← hr]
                      exact ih (Z + k0 + 3) (k0 + 1) _ _ _ r0 hrec k hk'
              | left =>
                  cases hrev : x.pre.reverse with
                  | nil => simp only [passRun, hpk, hrev] at hpass; cases hpass
                  | cons cq preRev =>
                      rw [passRun_left_unfold q b tab Z c hc x k0 (k1 :: L'') hb m' s' cq
                        preRev hrev hpk] at hpass
                      obtain ⟨r0, hrec, hr⟩ := Option.map_eq_some_iff.mp hpass
                      rw [← hr]
                      exact ih (Z + k0 + 3) (k0 + 1) _ _ _ r0 hrec k hk'

/-- 块列表的末块就是哨兵 `B`。The last block is the sentinel `B`. -/
theorem branchBlocks_getLast (B T i : Nat) : (branchBlocks B T i).getLast? = some B := by
  simp [branchBlocks]

/-- **哨兵保证终止**：分支上通路成功、且 `M.stutter` 的候选表长不超过 `B + 1`，
    则 `passEnd` 处的选号 `B + 1` 查表必然失败——多出来的那一轮在相位 4 死掉，
    不改变读数。这样「预算用尽」不会带来 `T + 1` 步的假接受。
    The sentinel makes the extra round fail its lookup in phase 4, so no false accept
    at step `T + 1` can occur. -/
theorem branch_sentinel_pick_none (q b B T i : Nat) (M : NTM q)
    (hl : ∀ m a, ((M.stutter).step m a).length ≤ B + 1)
    (hb : B + 2 < 2 ^ b) (hB : 0 < B)
    (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (r : PassRes q b)
    (hpass : passRun q b (M.stutter).step Z c hc x (branchBlocks B T i)
      (branchBlocks_hb B T i b hB hb) = some r) :
    pick ((M.stutter).step r.reg.state r.reg.cur) r.c = none := by
  have hlast := passRun_getLast_c q b (M.stutter).step (branchBlocks B T i) Z c hc x
    (branchBlocks_hb B T i b hB hb) r hpass B (branchBlocks_getLast B T i)
  have hle : ((M.stutter).step r.reg.state r.reg.cur).length ≤ r.c := by
    rw [hlast]
    exact hl r.reg.state r.reg.cur
  exact pick_eq_none_of_le _ _ hle

/-- 占位机的候选表长不超过原机上界 `B` 加一（序号 0 是空转动作）。
    The stutter candidate lists are at most `B + 1` long. -/
theorem stutter_step_length_le {q : Nat} (M : NTM q) (B : Nat)
    (hB : ∀ s a, (M.step s a).length ≤ B) :
    ∀ m a, ((M.stutter).step m a).length ≤ B + 1 := by
  intro m a
  simp only [NTM.stutter, List.length_cons]
  exact Nat.succ_le_succ (hB m a)

end DTM

end Pnp
