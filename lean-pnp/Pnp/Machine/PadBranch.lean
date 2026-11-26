/-
  文件：Pnp/Machine/PadBranch.lean
  主题：分支级总收口——观察机在预算内命中接受哨兵 ⇒ 原非确定机在 `T` 步内接受。
        初始区域只要求「与 `M.init w` 差两端空白格」（`Tape.SameInf`），
        因此兼容外层枚举的空白预留（auto-run-log #107/#108/#111）。

  Branch-level closure: an observer accept hit within budget implies
  `M.AcceptsWithin w T`, provided the initial region agrees with `M.init w` up to
  trailing blanks.  Composes `passRun_accept_prefix_of_obs_acc` (#110),
  `passRun_reg` and `acceptsWithin_of_stepCs_pad` (#111).
-/

import Pnp.Machine.PadVerdict
import Pnp.Machine.SimRoundM

set_option maxHeartbeats 800000

namespace Pnp

namespace DTM

/-- 观察上下文里驱动层的第 `i` 步格局（通路从区域 `x` 起跑）。 -/
def obsRun (q b : Nat) (M : NTM q) (x : Reg q) (m c Z : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (L : List Nat) (i : Nat) : Config (stateCountD q b) :=
  ((simDrive q b (M.haltNorm).step) (M.haltNorm).start).run i
    (passStart x m c hm hc Z L)

/-- 观察机的初始格局（驱动起点状态的重编码 + 纸带）。 -/
def obsStart (q b : Nat) (M : NTM q) (x : Reg q) (m c Z : Nat) (hm : m < q)
    (hc : c < 2 ^ b) (L : List Nat) : Config (stateCountO q b) :=
  Config.mk (embO q b (passStart x m c hm hc Z L).state)
    (passStart x m c hm hc Z L).tape

/-- **分支级总收口**：通路成功、预算内无内部接受态、观察机在 `r.steps` 内命中接受
    哨兵，且初始区域与 `M.init w` 只差两端空白 ⇒ `M` 在 `T` 步内接受。
    Observer accept hit (padded initial region) implies acceptance within `T`. -/
theorem acceptsWithin_of_obs_acc_pad (q b : Nat) (M : NTM q) (w : List Bool) (T : Nat)
    (Z c : Nat) (hc : c < 2 ^ b)
    (x : Reg q) (m : Nat) (hm : m < q)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (hxok : x.MarkersOK)
    (hst : x.state = M.start)
    (hxt : Tape.SameInf x.toConfig.tape (M.init w).tape)
    (L : List Nat) (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b)
    (hpadpost : L.length ≤ x.post.length)
    (hpadpre : L.length ≤ x.pre.length)
    (hlenT : L.length ≤ T)
    (r : PassRes q b)
    (hpass : passRun q b (M.haltNorm).step Z c hc x L hb = some r)
    (hnoacc : ∀ i : Nat, i < r.steps →
      ∀ (h : (obsRun q b M x m c Z hm hc L i).state.val < stateCount q b),
        unpackM (2 ^ b) 9 15 (obsRun q b M x m c Z hm hc L i).state.val
          ≠ (M.haltNorm).accept.val)
    (n : Nat) (hn : n ≤ r.steps)
    (hacc : ((simObs q b (M.haltNorm)).run n (obsStart q b M x m c Z hm hc L)).state
      = obsAcc q b) :
    M.AcceptsWithin w T := by
  -- 观察命中 ⇒ 接受前缀通路（#110）
  obtain ⟨L1, L2, hL, hb1, r1, hpass1, hstate1⟩ :=
    passRun_accept_prefix_of_obs_acc q b (M.haltNorm) L Z c hc x m hm hx
      hxok.1 hxok.2 hb hpadpost hpadpre r hpass hnoacc n hn hacc
  -- 前缀长度不超过预算
  have hlen1 : L1.length ≤ T := by
    have hle : L1.length ≤ L.length := by
      rw [hL]
      simp only [List.length_append]
      omega
    omega
  -- 前缀通路 ⇒ 区域按选择列表迭代到接受态
  have hreg := passRun_reg q b (M.haltNorm).step L1 c Z hc x hb1 r1 hpass1
  have hlen2 : (passChoices c L1).length ≤ T := by
    rw [passChoices_length]
    exact hlen1
  -- 空白版桥接：区域迭代 ⇒ 原机接受（#111）
  exact acceptsWithin_of_stepCs_pad q M (passChoices c L1) x r1.reg w T
    hxok hst hxt hreg hlen2 hstate1

end DTM

end Pnp
