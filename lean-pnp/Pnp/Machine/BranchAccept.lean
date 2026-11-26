/-
  文件：Pnp/Machine/BranchAccept.lean
  File: Pnp/Machine/BranchAccept.lean

  主题：接受方向的「分支块前缀通路」——原机在 `T` 步内接受 ⇒ 存在一个分支下标 `i < B^T`、
        一个轮数 `t ≤ T`，使该分支数字块列表的前 `t - 1` 块（再加哑元 `0`）在占位机上
        走通，且通路终态区域为接受态。
  Topic: the accept direction. If the original machine accepts within `T` steps, then some
  branch `i < B^T` admits a successful prefix pass over its block list, ending in accept.

  证明链（auto-run-log 承接 #113/#114/#117/#137）：
    1. `acceptsWithin_iff_exists_index`：接受 ⇒ 存在下标 `i` 与运行；
    2. `NTM.stutter_runWith`：占位机按「选择整体 +1」复现该运行；
    3. `exists_stepNs_take_accept_of_runWith`：得到计数迭代 `stepNs` 停在接受态；
    4. `exists_stepCs_take_accept_of_stepNs`：得到无计数折叠 `stepCs` 沿真前缀成功；
    5. `exists_passRun_of_stepCs_map`：把折叠成功翻译成通路成功。
  Proof chain: index representation, stutter replay, counted iteration, uncounted fold over a
  genuine prefix, and finally pass-run completeness.
-/

import Pnp.Machine.SimPassRev
import Pnp.Machine.SimStepCs
import Pnp.Machine.Stutter
import Pnp.Machine.BranchBlocks
import Pnp.IndexedSimulation

set_option maxHeartbeats 800000

namespace Pnp

namespace DTM

/-- 解码序列的首项（`T > 0`）：`seqOfIndex B T i` 的头部为 `i % B`。
    The head of the decoded sequence is `i % B` when `T > 0`. -/
theorem seqOfIndex_head? (B T i : Nat) (hT : 0 < T) :
    (seqOfIndex B T i).head? = some (i % B) := by
  cases T with
  | zero => omega
  | succ T' => rfl

/-- 前缀的「去掉首项后再整体减一」等于原列表去掉首项的同长前缀：
    `(((l.map (+1)).take n).drop 1).map (·-1) = (l.drop 1).take (n-1)`。
    Dropping the head of a `+1`-shifted prefix and subtracting one recovers the
    corresponding prefix of the original list. -/
theorem map_pred_drop_take_succ (l : List Nat) (n : Nat) :
    (((l.map (fun x => x + 1)).take n).drop 1).map (fun x => x - 1)
      = (l.drop 1).take (n - 1) := by
  rw [← List.map_take]
  rw [← List.map_drop]
  rw [List.map_map]
  rw [List.drop_take]
  apply List.map_id''
  intro x
  simp only [Function.comp_apply]
  omega

/-- **接受 ⇒ 分支族的成功通路**：若原机在 `T` 步内接受，则存在分支下标 `i < B^T` 与轮数
    `t ≤ T`，使「`t` 轮版」分支的数字块列表 `branchBlocks B t i` 在占位机上走通，且通路终态
    区域为接受态。`branchBlocks B t i` 是「长表 `branchBlocks B T i` 的前缀 + 哨兵 `B`」，
    末块哨兵保证通路之后多出的一轮查表失败（见 `branch_sentinel_pick_none`）。
    Acceptance yields a successful pass over a member of the branch family
    `branchBlocks B t i` (`1 ≤ t ≤ T`, `i < B^T`), ending in the accepting state. -/
theorem exists_pass_branchBlocks_of_acceptsWithin {q : Nat} (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T)
    (Z : Nat) (x : Reg q) (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hd1 : T ≤ x.pre.length) (hd2 : T ≤ x.post.length)
    (hxacc : x.state ≠ M.accept)
    (hacc : M.AcceptsWithin w T) :
    ∃ (t i : Nat) (r : PassRes q b),
      1 ≤ t ∧ t ≤ T ∧ i < B ^ T ∧
      passRun q b ((M.stutter).haltNorm).step Z (seqHead B T i)
        (seqHead_lt_pow B t i b hBpos hbnd) x
        (branchBlocks B t i) (branchBlocks_hb B t i b hBpos hbnd) = some r ∧
      r.reg.state = (M.stutter).haltNorm.accept := by
  -- 1. 下标表示：接受运行可写成某个 `i < B^T` 的解码序列
  obtain ⟨i, hi, c, hrun, hcacc⟩ :=
    (acceptsWithin_iff_exists_index hB hBpos w T).mp hacc
  -- 记解码序列与其 +1 平移（占位机的选择序列）；二者长度均为 T
  let s := seqOfIndex B T i
  let cs := s.map (fun y => y + 1)
  have hcs_len : cs.length = T := by
    dsimp only [cs, s]
    rw [List.length_map, seqOfIndex_length]
  -- 2. 占位机按「整体 +1」的选择序列复现运行
  have h1 : (M.stutter).runWith T (s.map (fun y => y + 1)) (M.init w) = some c := by
    rw [NTM.stutter_runWith]
    exact hrun
  -- 空白预留不改变运行：把 `M.init w` 侧的成功运行搬到区域侧
  obtain ⟨c2, hrun_s, hst⟩ :=
    NTM.runWith_cfgEquiv (M.stutter) T (s.map (fun y => y + 1)) hxw.symm c h1
  have hcacc2 : c2.state = (M.stutter).accept := by rw [← hst]; exact hcacc
  -- 3. 计数迭代在某个接受态停机，消耗真正前缀 `cs.take t`
  obtain ⟨t, z, htT0, htlen, hstepNs, hzacc, hzc⟩ :=
    exists_stepNs_take_accept_of_runWith (M.stutter) T
      (s.map (fun y => y + 1)) x c2 hx hd1 hd2 hrun_s hcacc2
  have htT : t ≤ T := by rw [← hcs_len]; exact htlen
  -- `t = 0` 时迭代原地返回 `x`，与「起点非接受」矛盾
  have htpos : 1 ≤ t := by
    rcases Nat.eq_zero_or_pos t with h0 | hpos
    · subst h0
      simp only [stepNs, Option.some.injEq] at hstepNs
      subst hstepNs
      exact absurd hzacc hxacc
    · exact hpos
  -- 4. 无计数折叠沿真前缀 `cs.take t'` 成功
  obtain ⟨t', ht'_le_t, ht'len, hstepCsraw⟩ :=
    exists_stepCs_take_accept_of_stepNs (M.stutter) t (cs.take t) x z hstepNs hzacc
  have hlen_take : (cs.take t).length = t := by
    rw [List.length_take, Nat.min_eq_left htlen]
  have ht'cs : t' ≤ cs.length := by omega
  have ht'T : t' ≤ T := by rw [← hcs_len]; exact ht'cs
  -- 把 `(cs.take t).take t'` 改写成 `cs.take t'`
  have hstepCs : stepCs ((M.stutter).haltNorm).step (cs.take t') x = some z := by
    rw [List.take_take, Nat.min_eq_left ht'_le_t] at hstepCsraw
    exact hstepCsraw
  -- `t' = 0` 时折叠原地返回 `x`，同样与「起点非接受」矛盾
  have ht'pos : 1 ≤ t' := by
    rcases Nat.eq_zero_or_pos t' with h0 | hpos
    · subst h0
      simp only [List.take_zero, stepCs, Option.some.injEq] at hstepCs
      subst hstepCs
      exact absurd hzacc hxacc
    · exact hpos
  -- 5. 前缀非空，拆成「首项 + 其余」
  have hσlen : (cs.take t').length = t' := by
    rw [List.length_take, Nat.min_eq_left ht'cs]
  have hσne : (cs.take t') ≠ [] := by
    intro hnil
    have h0 : (cs.take t').length = 0 := by rw [hnil]; rfl
    rw [hσlen] at h0
    omega
  -- 解码序列首项的头部是 `i % B`，故选择序列（+1）的头部是 `seqHead`
  have hsne : s ≠ [] := by
    intro hnil
    have h0 : s.length = 0 := by rw [hnil]; rfl
    dsimp only [s] at h0
    rw [seqOfIndex_length] at h0
    omega
  have hs_head : s.head hsne = i % B := by
    have h1 : s.head? = some (s.head hsne) := List.head?_eq_some_head hsne
    have h2 : s.head? = some (i % B) := by
      dsimp only [s]
      exact seqOfIndex_head? B T i hT
    rw [h1] at h2
    exact Option.some.inj h2
  have hσ_head? : (cs.take t').head? = some (seqHead B T i) := by
    rw [List.head?_take]
    split
    · omega
    · dsimp only [cs]
      rw [List.head?_map]
      dsimp only [s]
      rw [seqOfIndex_head? B T i hT]
      simp only [seqHead, Option.map_some]
  have hσ_head : (cs.take t').head hσne = seqHead B T i := by
    apply Option.some.inj
    rw [← List.head?_eq_some_head hσne]
    exact hσ_head?
  -- 分解式：`cs.take t' = seqHead :: rest`（其中 `rest = (cs.take t').drop 1`）
  let rest := (cs.take t').drop 1
  have hdec : (cs.take t').head hσne :: rest = cs.take t' := by
    dsimp only [rest]
    rw [List.drop_one]
    exact List.cons_head_tail hσne
  have hstepCs' : stepCs ((M.stutter).haltNorm).step (seqHead B T i :: rest) x = some z := by
    rw [← hσ_head, hdec]
    exact hstepCs
  -- 其余各项均 ≥ 1（它们是解码位 `d < B` 的 `d + 1`）
  have hpos : ∀ y ∈ rest, 1 ≤ y := by
    intro y hy
    dsimp only [rest] at hy
    have hycs : y ∈ cs := List.mem_of_mem_take (List.mem_of_mem_drop hy)
    dsimp only [cs] at hycs
    obtain ⟨d, hd, hfy⟩ := List.mem_map.mp hycs
    omega
  -- 前缀块列表的等价形式：`rest` 减一即原解码序列去掉首项的同长前缀
  have hrestmap : rest.map (fun y => y - 1) = (s.drop 1).take (t' - 1) := by
    dsimp only [rest, cs]
    exact map_pred_drop_take_succ s t'
  have hcZ : seqHead B T i < 2 ^ b := seqHead_lt_pow B T i b hBpos hbnd
  -- 分支块列表 = 前缀块 + 哨兵，故其选择序列正是 `seqHead :: rest`（末块值不影响选择）
  have hchoice : passChoices (seqHead B T i) (branchBlocks B t' i) = seqHead B T i :: rest := by
    rw [branchBlocks_eq_prefix ht'T, List.drop_take, ← hrestmap]
    exact passChoices_map_pred_append B rest hpos (seqHead B T i)
  have hstepCsQ : stepCs ((M.stutter).haltNorm).step
      (passChoices (seqHead B T i) (branchBlocks B t' i)) x = some z := by
    rw [hchoice]
    exact hstepCs'
  -- 6. 通路完备性：把折叠成功翻译成通路成功（块列表即分支族成员）
  obtain ⟨r, hpass, hreg⟩ :=
    exists_passRun_of_stepCs q b ((M.stutter).haltNorm).step
      (branchBlocks B t' i) Z (seqHead B T i) hcZ x z
      (branchBlocks_hb B t' i b hBpos hbnd) hstepCsQ
  refine ⟨t', i, r, ht'pos, ht'T, hi, hpass, ?_⟩
  -- 终态区域为接受态（`haltNorm.accept` 与 `stutter.accept` 定义上相同）
  rw [hreg]
  exact hzacc

end DTM

end Pnp
