/-
  文件：Pnp/Machine/SimAcceptObs.lean
  主题：把接受方向的语义完备性接到「观察机命中 `obsAcc`」——外层枚举的**完备性**
        （存在接受分支 ⇒ 该分支的观察机必在预算内命中接受哨兵）。

  链路（承接 SimAcceptComplete + SimHitComplete #116）：
    `M.AcceptsWithin w T`
      --exists_passRun_accept_of_acceptsWithin-->  成功通路 `passRun`，终态区域接受；
      --exists_obs_acc_of_passRun_accept  (#116)--> 观察机在 `r.steps` 内命中 `obsAcc`。

  前提 `x.state ≠ M.accept`：保证通路数字列表非空（空列表意味着起点已是接受态，
  此时另作平凡处理）；枚举起点为 `M.start` 时该前提成立（`InNP` 机器再需 `start ≠ accept`）。

  Completeness of the enumerator's accept branch: acceptance yields an observer hit of the
  accept sentinel within the pass length.
-/

import Pnp.Machine.SimAcceptComplete
import Pnp.Machine.SimHitComplete

namespace Pnp

namespace DTM

/-- **接受 ⇒ 观察命中**：若 `M` 在 `T` 步内接受 `w`，模拟区起点 `x` 与 `M.init w` 逐字一致、
    两侧空白足够、且起点状态不是接受态，则在占位机 `M.stutter` 的规范形下，存在一条数字
    列表 `L`，使观察机在通路步数预算内命中接受哨兵 `obsAcc`。
    Acceptance yields an observer hit of the accept sentinel within the pass-length budget. -/
theorem exists_obsAcc_of_acceptsWithin {q : Nat} (M : NTM q) {B : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (T : Nat) (b : Nat) (hbnd : B + 2 < 2 ^ b)
    (Z : Nat) (x : Reg q) (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hd1 : T ≤ x.pre.length) (hd2 : T ≤ x.post.length)
    (hxacc : x.state ≠ M.accept)
    (hacc : M.AcceptsWithin w T) :
    ∃ (L : List Nat) (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) (c : Nat) (hc : c < 2 ^ b)
      (n : Nat),
      ((simObs q b (M.stutter.haltNorm)).run n
        (obsStart q b (M.stutter) x x.state.val c Z x.state.isLt hc L)).state
        = obsAcc q b := by
  -- 先拿到接受通路
  obtain ⟨L, hb, c, hc, r, hpass, hracc⟩ :=
    exists_passRun_accept_of_acceptsWithin M hB hBpos w T b hbnd Z x hx hxw hd1 hd2 hacc
  -- 通路数字列表非空（否则起点即接受态，与 `hxacc` 矛盾）
  have hLne : L ≠ [] := by
    intro hL
    subst hL
    rw [show passRun q b (M.stutter.haltNorm).step Z c hc x [] hb
          = some ⟨0, Z, c, hc, x⟩ from rfl] at hpass
    have hr : (⟨0, Z, c, hc, x⟩ : PassRes q b) = r := Option.some.inj hpass
    have hregx : r.reg = x := by rw [← hr]
    exact hxacc (by rw [← hregx]; exact hracc)
  -- 观察机在 `r.steps` 内命中接受哨兵（#116），取出命中时刻 `n`
  obtain ⟨n, _hn, hhit⟩ :=
    exists_obs_acc_of_passRun_accept q b (M.stutter) L hLne Z c hc x x.state.val
      x.state.isLt rfl hx.1 hx.2 hb r hpass hracc
  exact ⟨L, hb, c, hc, n, hhit⟩

end DTM

end Pnp
