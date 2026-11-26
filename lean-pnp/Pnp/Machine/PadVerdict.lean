/-
  文件：Pnp/Machine/PadVerdict.lean
  主题：带空白预留的初始区域，以及「区域迭代 ⇒ 原机接受」在空白预留下的版本。

  背景：外层枚举必须在模拟区两侧各留 ≥ 轮数格的空白（auto-run-log #107/#108），
  于是区域的 `toConfig` 与 `M.init w` 只能「相差两端空白格」。本文件给出：
    - `Reg.initReg`：按输入 `w` 与两侧预留格数 `kl`/`kr` 构造初始区域；
    - `Reg.initReg_sameInf`：`initReg` 的 `toConfig` 与 `M.init w` 语义相同；
    - `acceptsWithin_of_stepCs_pad`：区域按选择列表走到接受态 ⇒ 原机 `T` 步内接受。

  Padded initial region and the padding-aware "region run ⇒ machine accepts" bridge.
-/

import Pnp.Machine.PadInv
import Pnp.Machine.SimVerdict

namespace Pnp

namespace DTM

namespace Reg

/-- 带两侧空白预留的初始区域：输入 `w` 从当前格开始，`post` 尾部接 `kr` 个空格，
    `pre` 放 `kl` 个空格（离头最远在前，全部标记位为 0）。
    Padded initial region: input `w` at the head, `kl`/`kr` blank cells on both sides. -/
def initReg {q : Nat} (st : Fin q) (w : List Bool) (kl kr : Nat) : Reg q :=
  { state := st,
    pre := List.replicate kl (none, false),
    cur := (w.map some).headD none,
    post := ((w.map some).drop 1).map (fun s => (s, false)) ++
      List.replicate kr (none, false) }

/-- 初始区域的标记位全为 0。 -/
theorem initReg_markersOK {q : Nat} (st : Fin q) (w : List Bool) (kl kr : Nat) :
    (initReg st w kl kr).MarkersOK := by
  constructor
  · intro p hp
    simp only [initReg, List.mem_replicate] at hp
    obtain ⟨-, rfl⟩ := hp
    rfl
  · intro p hp
    simp only [initReg, List.mem_append, List.mem_replicate] at hp
    rcases hp with hp | ⟨-, rfl⟩
    · rcases List.mem_map.mp hp with ⟨b, -, rfl⟩
      rfl
    · rfl

/-- `(s, false)` 形式的格表，取第一分量后回到原符号列表。 -/
theorem map_fst_map_sym (l : List Sym) :
    (l.map (fun s => (s, false))).map Prod.fst = l := by
  induction l with
  | nil => rfl
  | cons s ss ih => simp only [List.map_cons, ih]

/-- `(none, false)` 重复表取第一分量后是空白重复表。 -/
theorem map_fst_replicate_none (k : Nat) :
    (List.replicate k ((none, false) : Sym × Bool)).map Prod.fst
      = List.replicate k (none : Sym) := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate_succ, List.map_cons, ih]

/-- 初始区域 `toConfig` 的左端：`kl` 个空白格。 -/
theorem initReg_toConfig_left {q : Nat} (st : Fin q) (w : List Bool) (kl kr : Nat) :
    (initReg st w kl kr).toConfig.tape.left = List.replicate kl (none : Sym) := by
  simp only [initReg, toConfig, List.map_reverse, map_fst_replicate_none,
    List.reverse_replicate]

/-- 初始区域的 `toConfig` 与 `Tape.ofInput w` 只差两端空白格。 -/
theorem initReg_sameInf {q : Nat} (st : Fin q) (w : List Bool) (kl kr : Nat) :
    Tape.SameInf (initReg st w kl kr).toConfig.tape (Tape.ofInput w) := by
  cases w with
  | nil =>
      refine ⟨kl, kr + 1, ?_, ?_⟩
      · simpa only [Tape.ofInput, List.nil_append] using initReg_toConfig_left st [] kl kr
      · simp only [initReg, toConfig, Tape.ofInput, List.map_nil, List.headD, List.drop,
          List.nil_append, List.map_append, map_fst_replicate_none, List.replicate_succ]
  | cons b bs =>
      refine ⟨kl, kr, ?_, ?_⟩
      · simpa only [Tape.ofInput, List.nil_append] using
          initReg_toConfig_left st (b :: bs) kl kr
      · simp only [initReg, toConfig, Tape.ofInput, List.map_cons, List.headD, List.drop,
          List.map_append, map_fst_replicate_none, map_fst_map_sym, List.nil_append,
          List.cons_append]

end Reg

/-- **空白预留下的接受桥接**：区域按选择列表（规范形）走到接受态，且初始区域
    与 `M.init w` 只差两端空白格，则原机在 `T` 步内接受。
    Padding-aware acceptance bridge from a region run. -/
theorem acceptsWithin_of_stepCs_pad (q : Nat) (M : NTM q)
    (cs : List Nat) (x y : Reg q) (w : List Bool) (T : Nat)
    (hx : x.MarkersOK)
    (hst : x.state = M.start)
    (ht : Tape.SameInf x.toConfig.tape (M.init w).tape)
    (hreg : stepCs (M.haltNorm).step cs x = some y)
    (hlen : cs.length ≤ T) (hacc : y.state = M.accept) :
    M.AcceptsWithin w T := by
  -- 区域迭代 ⇒（规范形）`runWith`
  have hrun := runWith_of_stepCs M cs x y hx hreg
  -- 终态停机：补齐到 `T` 步
  have hhalt : (M.haltNorm).halted y.toConfig = true := by
    simp [NTM.halted, NTM.haltNorm, Reg.toConfig, hacc]
  have hrun' := NTM.runWith_extend (M.haltNorm) cs.length cs x.toConfig y.toConfig
    hrun hhalt T [] hlen
  have hlen' : (cs ++ []).length ≤ T := by simpa using hlen
  -- 规范形与原机同语义，空白预留不改变接受行为
  refine (NTM.haltNorm_acceptsWithin M w T).mp ?_
  refine NTM.acceptsWithin_of_sameInf (M.haltNorm) w T x.toConfig ?_ ?_
    ⟨cs ++ [], hlen', y.toConfig, hrun', hacc⟩
  · -- 起点状态一致
    simpa only [Reg.toConfig, NTM.haltNorm] using hst
  · -- 纸带只差两端空白
    simpa only [NTM.init, NTM.haltNorm, Tape.ofInput] using ht

end DTM

end Pnp
