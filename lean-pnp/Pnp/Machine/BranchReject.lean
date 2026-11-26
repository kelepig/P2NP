/-
  文件：Pnp/Machine/BranchReject.lean

  主题：分支级拒绝判据（通路成功情形）——由「不接受」推出通路沿途读数都不是接受态，
        再套 `simObs_no_acc_budget_of_passRun_halt` 得「预算内不命中 `obsAcc`」。
  Topic: the branch-level reject criterion for a successful pass. `¬ AccepsWithin`
  forbids any accepting reading along the pass, and the budget verdict follows.

  要点：沿途读数若等于接受态，`passRun_accept_prefix` 会给出一个真前缀，其通路终态
  区域就是接受态；再把该前缀单独当作一条通路喂给 `acceptsWithin_of_passRun_accept`
  就得到 `AcceptsWithin`，与前提矛盾。
  Key: an accepting reading yields a proper prefix whose pass ends in the accept state;
  that prefix alone is an accepting pass, contradicting `¬ AcceptsWithin`.
-/

import Pnp.Machine.SimBudget
import Pnp.Machine.SimExhaustObs
import Pnp.Machine.BranchBlocks

set_option maxHeartbeats 800000

namespace Pnp

namespace DTM

/-- **沿途读数非接受**：`¬ AcceptsWithin` 下，成功通路（及其前缀）沿途任何模拟层
    读数都不是接受态。
    Under `¬ AcceptsWithin`, no simulated-layer reading along a successful pass accepts. -/
theorem no_accept_readings_of_passRun_some (q b : Nat) (M : NTM q) (w : List Bool) (T : Nat)
    (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q)) (hxM : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false) (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (hpadpost : L.length ≤ x.post.length) (hpadpre : L.length ≤ x.pre.length)
    (hlen : L.length ≤ T)
    (r : PassRes q b) (hpass : passRun q b (M.haltNorm).step Z c hc x L hb = some r)
    (hna : ¬ M.AcceptsWithin w T) :
    ∀ i : Nat, i < r.steps →
      ∀ (h : ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i
          (passStart x m c hm hc Z L)).state.val < stateCount q b),
        unpackM (2 ^ b) 9 15
          ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i
            (passStart x m c hm hc Z L)).state.val ≠ (M.haltNorm).accept.val := by
  intro i hi hlt hacc
  -- 读数等于接受态 ⇒ 存在真前缀，其通路终态区域就是接受态
  obtain ⟨L1, L2, hL, hb1, r1, hp1, hreg⟩ :=
    passRun_accept_prefix q b (M.haltNorm).step (M.haltNorm).start M.accept L Z c hc x m hm
      hx hpre hpost hb hpadpost hpadpre i hlt hacc
      (Or.inl ⟨r, hpass, Nat.le_of_lt hi⟩)
  -- 该前缀单独是一条接受通路 ⇒ `AcceptsWithin`，矛盾
  have hlen1 : L1.length ≤ T := by
    have hLlen : (L1 ++ L2).length ≤ T := by rw [← hL]; exact hlen
    rw [List.length_append] at hLlen
    omega
  exact passRun_not_accept_of_not_acceptsWithin q b M L1 Z c hc x hb1 r1 w T
    hxM hxw hlen1 hp1 hna hreg

/-- **分支级拒绝判据（通路成功）**：`¬ AcceptsWithin` + 通路成功 + 终态查表失败
    ⇒ 观察机跑满预算不在 `obsAcc`。
    Branch-level reject verdict for a successful pass. -/
theorem branch_no_acc_budget_of_passRun_some (q b : Nat) (M : NTM q) (w : List Bool) (T : Nat)
    (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q)) (hxM : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false) (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (hpadpost : L.length ≤ x.post.length) (hpadpre : L.length ≤ x.pre.length)
    (hlen : L.length ≤ T)
    (r : PassRes q b) (hpass : passRun q b (M.haltNorm).step Z c hc x L hb = some r)
    (hpk : pick ((M.haltNorm).step r.reg.state r.reg.cur) r.c = none)
    (hna : ¬ M.AcceptsWithin w T)
    (budget : Nat) (hbud : r.steps + 6 ≤ budget) :
    ((simObs q b (M.haltNorm)).run budget
      (Config.mk (embO q b (passStart x m c hm hc Z L).state)
        (passStart x m c hm hc Z L).tape)).state ≠ obsAcc q b :=
  simObs_no_acc_budget_of_passRun_halt q b M L Z c hc x m hm hx hpre hpost hb r hpass
    (no_accept_readings_of_passRun_some q b M w T L Z c hc x m hm hx hxM hxw hpre hpost hb
      hpadpost hpadpre hlen r hpass hna)
    (passRun_not_accept_of_not_acceptsWithin q b M L Z c hc x hb r w T hxM hxw hlen hpass hna)
    hpk budget hbud

/-- **分支级拒绝判据（通路失败）**：若通路在某个前缀后查表失败（`passRun = none`），
    则沿途任何读数都不是接受态；配上前缀的步数上界即可得「预算内不命中 `obsAcc`」。
    左右越界两种失败情形由区域填充（`L.length + 1 ≤ x.post.length` / `x.pre.length`）
    排除——填充保证失败只可能发生在前缀边界之前。
    Branch-level reject verdict for a failed pass. Overflow failures are excluded by the
    region padding, so the only possible failure is a failing table lookup. -/
theorem branch_no_acc_budget_of_passRun_none (q b : Nat) (M : NTM q) (w : List Bool) (T : Nat)
    (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q)) (hxM : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false) (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (hpadpost : L.length + 1 ≤ x.post.length) (hpadpre : L.length + 1 ≤ x.pre.length)
    (hlen : L.length ≤ T)
    (hpass : passRun q b (M.haltNorm).step Z c hc x L hb = none)
    (hna : ¬ M.AcceptsWithin w T)
    (N : Nat)
    (hN : ∀ (L1 : List Nat) (hb1 : ∀ k' ∈ L1, k' + 2 < 2 ^ b) (r1 : PassRes q b),
      L1.length ≤ T → passRun q b (M.haltNorm).step Z c hc x L1 hb1 = some r1 →
        r1.steps + 6 ≤ N)
    (budget : Nat) (hbud : N ≤ budget) :
    ((simObs q b (M.haltNorm)).run budget
      (Config.mk (embO q b (passStart x m c hm hc Z L).state)
        (passStart x m c hm hc Z L).tape)).state ≠ obsAcc q b := by
  -- 失败位置的分解：前缀成功 + 一步失败
  obtain ⟨L1, r1, k, ks, hL, ⟨hb1, hp1⟩, hfail⟩ :=
    passRun_none_decomp q b (M.haltNorm).step L Z c hc x hb hpass
  have hL1le : L1.length ≤ L.length := by rw [hL]; simp
  have hlen1 : L1.length ≤ T := by omega
  -- 填充排除左右越界：失败前缀之后区域至少还剩一格
  have hpost_ne : r1.reg.post ≠ [] := by
    have hge := passRun_post_ge q b (M.haltNorm).step L1 Z c hc x hb1 r1 hp1
    intro hnil
    rw [hnil, List.length_nil] at hge
    omega
  have hpre_ne : r1.reg.pre ≠ [] := by
    have hge := passRun_pre_ge q b (M.haltNorm).step L1 Z c hc x hb1 r1 hp1
    intro hnil
    rw [hnil, List.length_nil] at hge
    omega
  -- 沿途读数非接受：读数＝接受态会给出前缀，单独构成接受通路，与前提矛盾
  have hnoacc : ∀ i : Nat, i < r1.steps →
      ∀ (h : ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i
          (passStart x m c hm hc Z (L1 ++ (k :: ks)))).state.val < stateCount q b),
        unpackM (2 ^ b) 9 15
          ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i
            (passStart x m c hm hc Z (L1 ++ (k :: ks)))).state.val
          ≠ (M.haltNorm).accept.val := by
    intro i hi hlt hacc
    rw [← hL] at hlt hacc
    obtain ⟨L1', L2', hL', hb1', r1', hp1', hreg⟩ :=
      passRun_accept_prefix q b (M.haltNorm).step (M.haltNorm).start M.accept L Z c hc x m hm
        hx hpre hpost hb (by omega) (by omega) i hlt hacc (Or.inr hpass)
    have hlen1' : L1'.length ≤ T := by
      have hlt' : (L1' ++ L2').length ≤ T := by rw [← hL']; exact hlen
      rw [List.length_append] at hlt'
      omega
    exact passRun_not_accept_of_not_acceptsWithin q b M L1' Z c hc x hb1' r1' w T
      hxM hxw hlen1' hp1' hna hreg
  -- 前缀终态非接受
  have hxacc := passRun_not_accept_of_not_acceptsWithin q b M L1 Z c hc x hb1 r1 w T
    hxM hxw hlen1 hp1 hna
  -- 只有「查表失败」可行
  rcases hfail with hpk | ⟨m', s', _, hpost0⟩ | ⟨m', s', _, hpre0⟩
  · have hbud1 := hN L1 hb1 r1 hlen1 hp1
    rw [hL]
    exact simObs_no_acc_budget_of_prefix_fail q b M L1 (k :: ks) Z c hc x m hm hx hpre hpost
      hb1 r1 hp1 hnoacc hxacc hpk budget (by omega)
  · exact absurd hpost0 hpost_ne
  · exact absurd hpre0 hpre_ne

/-- **通路 + 终点判据 ⇒ 预算内不接受（通用合成）**：通路内用 `hnoacc`（观察投影到
    `passEnd`），通路后用 `hpe`（终点起的任意 `n ≤ budget − r.steps` 都不落 `obsAcc`）。
    拒绝方向的三个「通路后」情形（查表失败、耗尽轮三方向）共用这一合成。
    Generic composition: within the pass the readings are safe; after it, the verdict on
    `passEnd` covers the rest of the budget. -/
theorem simObs_no_acc_budget_of_passRun_passEnd (q b : Nat) (M : NTM q)
    (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (r : PassRes q b) (hpass : passRun q b (M.haltNorm).step Z c hc x L hb = some r)
    (hnoacc : ∀ i : Nat, i < r.steps →
      ∀ (h : ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i
          (passStart x m c hm hc Z L)).state.val < stateCount q b),
        unpackM (2 ^ b) 9 15
          ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i
            (passStart x m c hm hc Z L)).state.val ≠ (M.haltNorm).accept.val)
    (budget : Nat) (hbud : r.steps ≤ budget)
    (hpe : ∀ n : Nat, n ≤ budget - r.steps →
      ((simObs q b (M.haltNorm)).run n
        (Config.mk (embO q b (passEnd r).state) (passEnd r).tape)).state ≠ obsAcc q b) :
    ((simObs q b (M.haltNorm)).run budget
        (Config.mk (embO q b (passStart x m c hm hc Z L).state)
          (passStart x m c hm hc Z L).tape)).state ≠ obsAcc q b := by
  -- 通路内的可观察性 ⇒ 观察投影：`r.steps` 步后正是 `passEnd`
  have hobs := simObs_pass_obs q b (M.haltNorm) L Z c hc x m hm hx hpre hpost hb r hpass hnoacc
  have hdele := simObs_run_delegate q b (M.haltNorm) r.steps
    (passStart x m c hm hc Z L) (fun i hi => hobs i hi)
  have hpeq := simDrive_pass q b (M.haltNorm).step (M.haltNorm).start L Z c hc x m hm hx
    hpre hpost hb r hpass
  have hmid : (simObs q b (M.haltNorm)).run r.steps
      (Config.mk (embO q b (passStart x m c hm hc Z L).state)
        (passStart x m c hm hc Z L).tape) =
      Config.mk (embO q b (passEnd r).state) (passEnd r).tape := by
    rw [hdele, hpeq]
  -- 预算拆成「通路步数 + 余下步数」，后半段交给 `hpe`
  rw [show budget = r.steps + (budget - r.steps) from by omega, DTM.run_add, hmid]
  exact hpe (budget - r.steps) (Nat.le_refl _)

/-- **分支级拒绝判据（通路成功 + 耗尽轮原地）**。Exhaustion, stay direction. -/
theorem branch_no_acc_budget_of_passRun_exhaust_stay (q b : Nat) (M : NTM q)
    (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (r : PassRes q b) (hpass : passRun q b (M.haltNorm).step Z c hc x L hb = some r)
    (hnoacc : ∀ i : Nat, i < r.steps →
      ∀ (h : ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i
          (passStart x m c hm hc Z L)).state.val < stateCount q b),
        unpackM (2 ^ b) 9 15
          ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i
            (passStart x m c hm hc Z L)).state.val ≠ (M.haltNorm).accept.val)
    (m' : Fin q) (s' : Sym)
    (hpk : pick ((M.haltNorm).step r.reg.state r.reg.cur) r.c = some (m', s', Dir.stay))
    (hacc : m' ≠ (M.haltNorm).accept)
    (budget : Nat)
    (hbud : r.steps
      + (18 + (codeFst s' :: List.reverse (codeCells r.reg.pre)).length + r.z) ≤ budget) :
    ((simObs q b (M.haltNorm)).run budget
        (Config.mk (embO q b (passStart x m c hm hc Z L).state)
          (passStart x m c hm hc Z L).tape)).state ≠ obsAcc q b := by
  refine simObs_no_acc_budget_of_passRun_passEnd q b M L Z c hc x m hm hx hpre hpost hb r
    hpass hnoacc budget (by omega) ?_
  intro n hn
  have hrem : 18 + (codeFst s' :: List.reverse (codeCells r.reg.pre)).length + r.z
      ≤ budget - r.steps := by omega
  exact simObs_no_accept_budget_of_passEnd_exhaust_stay q b M r m' s' hpk hacc
    (budget - r.steps) hrem n hn

/-- **分支级拒绝判据（通路成功 + 耗尽轮右移）**。Exhaustion, right direction. -/
theorem branch_no_acc_budget_of_passRun_exhaust_right (q b : Nat) (M : NTM q)
    (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (r : PassRes q b) (hpass : passRun q b (M.haltNorm).step Z c hc x L hb = some r)
    (hnoacc : ∀ i : Nat, i < r.steps →
      ∀ (h : ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i
          (passStart x m c hm hc Z L)).state.val < stateCount q b),
        unpackM (2 ^ b) 9 15
          ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i
            (passStart x m c hm hc Z L)).state.val ≠ (M.haltNorm).accept.val)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (hp : p.2 = false)
    (hpostr : r.reg.post = p :: post') (m' : Fin q) (s' : Sym)
    (hpk : pick ((M.haltNorm).step r.reg.state r.reg.cur) r.c = some (m', s', Dir.right))
    (hacc : m' ≠ (M.haltNorm).accept)
    (budget : Nat)
    (hbud : r.steps
      + (18 + (codeFst p.1 :: List.reverse (codeCells (r.reg.pre ++ [(s', false)]))).length
        + r.z) ≤ budget) :
    ((simObs q b (M.haltNorm)).run budget
        (Config.mk (embO q b (passStart x m c hm hc Z L).state)
          (passStart x m c hm hc Z L).tape)).state ≠ obsAcc q b := by
  refine simObs_no_acc_budget_of_passRun_passEnd q b M L Z c hc x m hm hx hpre hpost hb r
    hpass hnoacc budget (by omega) ?_
  intro n hn
  have hrem : 18 + (codeFst p.1 :: List.reverse
      (codeCells (r.reg.pre ++ [(s', false)]))).length + r.z ≤ budget - r.steps := by omega
  exact simObs_no_accept_budget_of_passEnd_exhaust_right q b M r p post' hp hpostr m' s' hpk
    hacc (budget - r.steps) hrem n hn

/-- **分支级拒绝判据（通路成功 + 耗尽轮左移）**。Exhaustion, left direction. -/
theorem branch_no_acc_budget_of_passRun_exhaust_left (q b : Nat) (M : NTM q)
    (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false)
    (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (r : PassRes q b) (hpass : passRun q b (M.haltNorm).step Z c hc x L hb = some r)
    (hnoacc : ∀ i : Nat, i < r.steps →
      ∀ (h : ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i
          (passStart x m c hm hc Z L)).state.val < stateCount q b),
        unpackM (2 ^ b) 9 15
          ((simDrive q b (M.haltNorm).step (M.haltNorm).start).run i
            (passStart x m c hm hc Z L)).state.val ≠ (M.haltNorm).accept.val)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (hq : cq.2 = false)
    (hprer : r.reg.pre = pre' ++ [cq]) (m' : Fin q) (s' : Sym)
    (hpk : pick ((M.haltNorm).step r.reg.state r.reg.cur) r.c = some (m', s', Dir.left))
    (hacc : m' ≠ (M.haltNorm).accept)
    (budget : Nat)
    (hbud : r.steps
      + (18 + (codeFst cq.1 :: List.reverse (codeCells pre')).length + r.z) ≤ budget) :
    ((simObs q b (M.haltNorm)).run budget
        (Config.mk (embO q b (passStart x m c hm hc Z L).state)
          (passStart x m c hm hc Z L).tape)).state ≠ obsAcc q b := by
  refine simObs_no_acc_budget_of_passRun_passEnd q b M L Z c hc x m hm hx hpre hpost hb r
    hpass hnoacc budget (by omega) ?_
  intro n hn
  have hrem : 18 + (codeFst cq.1 :: List.reverse (codeCells pre')).length + r.z
      ≤ budget - r.steps := by omega
  exact simObs_no_accept_budget_of_passEnd_exhaust_left q b M r cq pre' hq hprer m' s' hpk
    hacc (budget - r.steps) hrem n hn

/-- **分支块的拒绝判据**：编码分支 `branchBlocks B T i`、区域两侧留足空白、原机在 `T'`
    步内不接受、预算 `K` 覆盖一切前缀通路步数 ⇒ 观察机（模拟占位机 `M.stutter`）跑满
    `K` 步不在 `obsAcc`。
    哨兵使得「通路成功后查表有候选」这一情形不可能出现（终态计数器为 `B + 1`，
    而候选表长 ≤ `B + 1`），故只需处理「通路成功 + 查表失败」与「通路中途失败」两种。
    Branch reject verdict for the encoded block list. The sentinel rules out the
    "pass succeeded but a rule still exists" shape, leaving two cases. -/
theorem branch_no_acc_budget_blocks (q b B T i : Nat) (M : NTM q) (w : List Bool) (T' : Nat)
    (hB : 0 < B) (hb : B + 2 < 2 ^ b)
    (hl : ∀ m a, ((M.stutter).step m a).length ≤ B + 1)
    (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q)) (hxM : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false) (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hpadpost : (branchBlocks B T i).length + 1 ≤ x.post.length)
    (hpadpre : (branchBlocks B T i).length + 1 ≤ x.pre.length)
    (hlen : (branchBlocks B T i).length ≤ T')
    (hna : ¬ M.AcceptsWithin w T')
    (K : Nat)
    (hK : ∀ (L1 : List Nat) (hb1 : ∀ k' ∈ L1, k' + 2 < 2 ^ b) (r1 : PassRes q b),
      L1.length ≤ T' →
      passRun q b ((M.stutter).haltNorm).step Z c hc x L1 hb1 = some r1 → r1.steps + 6 ≤ K) :
    ((simObs q b ((M.stutter).haltNorm)).run K
      (Config.mk (embO q b (passStart x m c hm hc Z (branchBlocks B T i)).state)
        (passStart x m c hm hc Z (branchBlocks B T i)).tape)).state ≠ obsAcc q b := by
  have hbl := branchBlocks_hb B T i b hB hb
  -- 原机不接受 ⇒ 占位机也不接受（选择索引整体 +1 下等价）
  have hna' : ¬ (M.stutter).AcceptsWithin w T' :=
    fun h => hna ((NTM.acceptsWithin_stutter_iff M w T').mp h)
  have hxw' : CfgEquiv x.toConfig ((M.stutter).init w) := hxw
  cases hpass : passRun q b ((M.stutter).haltNorm).step Z c hc x (branchBlocks B T i) hbl with
  | none =>
      -- 通路中途失败
      refine branch_no_acc_budget_of_passRun_none q b (M.stutter) w T'
        (branchBlocks B T i) Z c hc x m hm hx hxM hxw' hpre hpost hbl
        hpadpost hpadpre hlen hpass hna' K ?_ K (Nat.le_refl K)
      intro L1 hb1 r1 hle1 hp1
      exact hK L1 hb1 r1 hle1 hp1
  | some r =>
      -- 通路成功：终态计数器 = 哨兵 + 1 ⇒ 查表必失败
      have hlast : r.c = B + 1 :=
        passRun_getLast_c q b ((M.stutter).haltNorm).step (branchBlocks B T i) Z c hc x hbl
          r hpass B (branchBlocks_getLast B T i)
      have hxacc : r.reg.state ≠ (M.stutter).haltNorm.accept :=
        passRun_not_accept_of_not_acceptsWithin q b (M.stutter) (branchBlocks B T i) Z c hc
          x hbl r w T' hxM hxw' hlen hpass hna'
      have hpk : pick ((M.stutter).haltNorm.step r.reg.state r.reg.cur) r.c = none := by
        by_cases hrej : r.reg.state = (M.stutter).reject
        · exact pick_haltNorm_none (M.stutter) r.reg r.c (Or.inr hrej)
        · -- 非停机态：规范形与原占位机的转移表一致
          have hstep : (M.stutter).haltNorm.step r.reg.state r.reg.cur
              = (M.stutter).step r.reg.state r.reg.cur := by
            simp only [NTM.haltNorm]
            rw [if_neg]
            intro hh
            rcases hh with hh | hh
            · exact hxacc hh
            · exact hrej hh
          rw [hstep]
          refine pick_eq_none_of_le _ _ ?_
          rw [hlast]
          exact hl r.reg.state r.reg.cur
      exact branch_no_acc_budget_of_passRun_some q b (M.stutter) w T'
        (branchBlocks B T i) Z c hc x m hm hx hxM hxw' hpre hpost hbl
        (by omega) (by omega) hlen r hpass hpk hna' K (hK _ hbl r hlen hpass)


/-- `costCap` 对轮数单调（其余参数固定）。`costCap` is monotone in the round count. -/
theorem costCap_le_of_le (P Z T T' Bk : Nat) (h : T ≤ T') :
    costCap P Z T Bk ≤ costCap P Z T' Bk := by
  have h1 : T * (Bk + 3) ≤ T' * (Bk + 3) := Nat.mul_le_mul_right _ h
  have h2 : P + T ≤ P + T' := by omega
  have h3 : 6 * (P + T) ≤ 6 * (P + T') := Nat.mul_le_mul_left _ h2
  have h4 : Z + T * (Bk + 3) ≤ Z + T' * (Bk + 3) := by omega
  have h5 : 2 * (Z + T * (Bk + 3)) ≤ 2 * (Z + T' * (Bk + 3)) :=
    Nat.mul_le_mul_left _ h4
  simp only [costCap]
  omega

/-- **通路步数的统一预算**：块数不超过 `T'` 时，通路步数加 6 仍在 `T' · costCap + 6` 内。
    Uniform step budget for any pass with at most `T'` blocks. -/
theorem passRun_steps_le_uniform (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (ks : List Nat)
    (hb : ∀ k' ∈ ks, k' + 2 < 2 ^ b) (r : PassRes q b)
    (hpass : passRun q b tab Z c hc x ks hb = some r) (T' : Nat) (hlen : ks.length ≤ T') :
    r.steps + 6 ≤ T' * costCap x.pre.length Z T' (2 ^ b) + 6 := by
  have h1 := passRun_steps_le q b tab Z c hc x ks hb r hpass
  have h2 : ks.length * costCap x.pre.length Z ks.length (2 ^ b)
      ≤ T' * costCap x.pre.length Z T' (2 ^ b) :=
    Nat.mul_le_mul hlen (costCap_le_of_le x.pre.length Z ks.length T' (2 ^ b) hlen)
  omega

/-- **分支块的拒绝判据（统一预算）**：预算取 `T' · costCap + 6`，覆盖一切前缀通路
    （`passRun_steps_le_uniform`）。这是外层枚举「逐分支判非接受」的直接接口。
    The branch reject verdict with the uniform budget `T' · costCap + 6`. -/
theorem branch_no_acc_budget_blocks_uniform (q b B T i : Nat) (M : NTM q) (w : List Bool)
    (T' : Nat)
    (hB : 0 < B) (hb : B + 2 < 2 ^ b)
    (hl : ∀ m a, ((M.stutter).step m a).length ≤ B + 1)
    (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q)) (hxM : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false) (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hpadpost : (branchBlocks B T i).length + 1 ≤ x.post.length)
    (hpadpre : (branchBlocks B T i).length + 1 ≤ x.pre.length)
    (hlen : (branchBlocks B T i).length ≤ T')
    (hna : ¬ M.AcceptsWithin w T') :
    ((simObs q b ((M.stutter).haltNorm)).run
      (T' * costCap x.pre.length Z T' (2 ^ b) + 6)
      (Config.mk (embO q b (passStart x m c hm hc Z (branchBlocks B T i)).state)
        (passStart x m c hm hc Z (branchBlocks B T i)).tape)).state ≠ obsAcc q b := by
  refine branch_no_acc_budget_blocks q b B T i M w T' hB hb hl Z c hc x m hm hx hxM hxw
    hpre hpost hpadpost hpadpre hlen hna _ ?_
  intro L1 hb1 r1 hle1 hp1
  exact passRun_steps_le_uniform q b ((M.stutter).haltNorm).step Z c hc x L1 hb1 r1 hp1 T' hle1


/-- **分支命中 ⇒ 接受（可靠性）**：在统一预算 `T'·costCap+6` 内观察机命中 `obsAcc`
    就排除了「`M` 不接受」，故 `M` 在 `T'` 步内接受。这是外层枚举「某分支命中 ⇒ 接受」
    的语义接口（由拒绝判据的逆否直接给出）。
    A branch's accept hit at the uniform budget rules out non-acceptance. -/
theorem acceptsWithin_of_branch_hit (q b B T i : Nat) (M : NTM q) (w : List Bool)
    (T' : Nat)
    (hB : 0 < B) (hb : B + 2 < 2 ^ b)
    (hl : ∀ m a, ((M.stutter).step m a).length ≤ B + 1)
    (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q)) (hxM : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hpre : ∀ p0 ∈ x.pre, p0.2 = false) (hpost : ∀ p0 ∈ x.post, p0.2 = false)
    (hpadpost : (branchBlocks B T i).length + 1 ≤ x.post.length)
    (hpadpre : (branchBlocks B T i).length + 1 ≤ x.pre.length)
    (hlen : (branchBlocks B T i).length ≤ T')
    (hHit : ((simObs q b ((M.stutter).haltNorm)).run
      (T' * costCap x.pre.length Z T' (2 ^ b) + 6)
      (Config.mk (embO q b (passStart x m c hm hc Z (branchBlocks B T i)).state)
        (passStart x m c hm hc Z (branchBlocks B T i)).tape)).state = obsAcc q b) :
    M.AcceptsWithin w T' := by
  exact Classical.byContradiction (fun hna =>
    branch_no_acc_budget_blocks_uniform q b B T i M w T' hB hb hl Z c hc x m hm hx
      hxM hxw hpre hpost hpadpost hpadpre hlen hna hHit)

end DTM

end Pnp
