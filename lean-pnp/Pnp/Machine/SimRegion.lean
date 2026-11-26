/-
  文件：Pnp/Machine/SimRegion.lean
  主题：把单带模拟器的「被模拟纸带」抽象成**区域**（`Reg`），并证明
        「一轮 14 步」在区域层面就是被模拟机的一步。

  背景：`SimAll.lean` 已证明三个方向的整轮（13 步）与「整轮 + 重启」（14 步），
  但都是针对具体纸带形状（`Tape.mk (codeSnd s :: codeFst s :: …) …`）写的。
  多轮归纳需要在「状态 + 头位置 + 两侧格」这一层描述纸带，否则每一轮都要
  重新拆一次列表。

  本文件给出：
    - `Reg`：被模拟格局（状态、头左侧格、当前符号、头右侧格）；
    - `Reg.enc`：区域到物理纸带的编码（与 `simAll_round_*14` 的形状一致）；
    - `Reg.MarkersOK`：两侧所有格的标记位都是 0（头标记只由 `cur` 体现）；
    - 编码边界的化简引理 `enc_pre_snoc` / `enc_pre_last` / `enc_left_out`；
    - 三个方向的 14 步包装 `simAll_round_{stay,right,left}_enc`（以 `Reg` 表述）。

  说明：端外移动（头走到区域尽头再往外）不在本文件的抽象里；驱动机会在区域
  两端预置足够的空白格（`docs/07-B5-模拟器设计.md`），因此每一轮都能落在区域内。
-/

import Pnp.Machine.SimAll
import Pnp.Machine.PadInv
import Pnp.Search
import Pnp.TapeEncoding

namespace Pnp

namespace DTM

/-- 被模拟格局：状态、头左侧格（远 → 近）、当前符号、头右侧格（近 → 远）。
    当前格的头标记固定为 `some true`，不重复存进格数据。 -/
structure Reg (q : Nat) where
  /-- 被模拟机的当前状态。 -/
  state : Fin q
  /-- 头左侧的格（离头最远的在前）。 -/
  pre : List (Sym × Bool)
  /-- 头当前格的符号。 -/
  cur : Sym
  /-- 头右侧的格（离头最近的在前）。 -/
  post : List (Sym × Bool)

namespace Reg

/-- 区域到物理纸带的编码：左侧是头左格编码的逆序加后缀 `L`，
    右侧是头标记加右侧格编码。 -/
def enc {q : Nat} (x : Reg q) (L : List Sym) : Tape :=
  Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
          ((some true) :: codeCells x.post)

/-- 区域良构：两侧所有格的标记位都是 0（头标记由 `enc` 单独写出）。 -/
def MarkersOK {q : Nat} (x : Reg q) : Prop :=
  (∀ p ∈ x.pre, p.2 = false) ∧ (∀ p ∈ x.post, p.2 = false)

end Reg

/-- 右移之后的纸带形状 = 新区域的编码（老的头格进入 `pre`，标记写 0）。 -/
theorem enc_pre_snoc {q : Nat} (st : Fin q) (pre : List (Sym × Bool)) (p : Sym × Bool)
    (s' : Sym) (post' : List (Sym × Bool)) (L : List Sym) :
    Tape.mk (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' ::
        (List.reverse (codeCells pre) ++ L)) ((some true) :: codeCells post') =
      Reg.enc { state := st, pre := pre ++ [(s', false)], cur := p.1, post := post' } L := by
  simp only [Reg.enc, codeCells, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    cellCode, symCode_eq, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.append_nil, List.cons_append, List.singleton_append,
    List.append_assoc, Bool.false_eq_true, ite_false]

/-- 头左侧最后一格是 `cq` 时，区域编码展开成「前格编码 + 后缀」的形状。 -/
theorem enc_pre_last {q : Nat} (st : Fin q) (pre' : List (Sym × Bool)) (cq : Sym × Bool)
    (s : Sym) (post : List (Sym × Bool)) (L : List Sym) (hq : cq.2 = false) :
    Reg.enc { state := st, pre := pre' ++ [cq], cur := s, post := post } L =
      Tape.mk (codeSnd s :: codeFst s :: (some false) :: codeSnd cq.1 :: codeFst cq.1 ::
        (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells post) := by
  simp only [Reg.enc, codeCells, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    cellCode, symCode_eq, hq, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.append_nil, List.cons_append, List.singleton_append,
    List.append_assoc, Bool.false_eq_true, ite_false]

/-- 左移之后的纸带形状 = 新区域的编码（新的头格是老的左邻格 `cq`）。 -/
theorem enc_left_out {q : Nat} (st : Fin q) (pre' : List (Sym × Bool)) (cq : Sym × Bool)
    (s' : Sym) (post : List (Sym × Bool)) (L : List Sym) :
    Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L))
        ((some true) :: codeFst s' :: codeSnd s' :: (some false) :: codeCells post) =
      Reg.enc { state := st, pre := pre', cur := cq.1, post := (s', false) :: post } L := by
  simp only [Reg.enc, codeCells, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    cellCode, symCode_eq, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.append_nil, List.cons_append, List.singleton_append,
    List.append_assoc, Bool.false_eq_true, ite_false]

/-- `simAll` 一整轮 + 重启（原地），以区域表述。 -/
theorem simAll_round_stay_enc (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (hk1 : k + 1 < T)
    (c : Nat) (hc : c < 2 ^ b) (x : Reg q) (L : List Sym)
    (m' : Fin q) (s' : Sym)
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.stay)) :
    (simAll q b T hT tab s0).run 14
      (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (x.enc L)) =
    Config.mk (embK q b T (k + 1) hk1
        (codeState q b m'.val c 0 0 m'.isLt hc (by decide) (by decide)))
      (({ state := m', pre := x.pre, cur := s', post := x.post } : Reg q).enc L) := by
  exact simAll_round_stay14 q b T hT tab s0 k hk hk1 x.state.val c x.state.isLt hc
    x.cur x.pre x.post L m' s' h

/-- `simAll` 一整轮 + 重启（右移），以区域表述。 -/
theorem simAll_round_right_enc (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (hk1 : k + 1 < T)
    (c : Nat) (hc : c < 2 ^ b) (x : Reg q) (L : List Sym)
    (p : Sym × Bool) (post' : List (Sym × Bool))
    (hp : p.2 = false) (hpost : x.post = p :: post')
    (m' : Fin q) (s' : Sym)
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.right)) :
    (simAll q b T hT tab s0).run 14
      (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (x.enc L)) =
    Config.mk (embK q b T (k + 1) hk1
        (codeState q b m'.val c 0 0 m'.isLt hc (by decide) (by decide)))
      (({ state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } :
        Reg q).enc L) := by
  obtain ⟨st, pre, cur, post⟩ := x
  simp only at hpost
  subst hpost
  have hmain := simAll_round_right14 q b T hT tab s0 k hk hk1 st.val c st.isLt hc
    cur p post' pre L hp m' s' h
  rw [← enc_pre_snoc m' pre p s' post' L]
  exact hmain

/-- `simAll` 一整轮 + 重启（左移），以区域表述。 -/
theorem simAll_round_left_enc (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (hk1 : k + 1 < T)
    (c : Nat) (hc : c < 2 ^ b) (x : Reg q) (L : List Sym)
    (cq : Sym × Bool) (pre' : List (Sym × Bool))
    (hq : cq.2 = false) (hpre : x.pre = pre' ++ [cq])
    (m' : Fin q) (s' : Sym)
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.left)) :
    (simAll q b T hT tab s0).run 14
      (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (x.enc L)) =
    Config.mk (embK q b T (k + 1) hk1
        (codeState q b m'.val c 0 0 m'.isLt hc (by decide) (by decide)))
      (({ state := m', pre := pre', cur := cq.1, post := (s', false) :: x.post } :
        Reg q).enc L) := by
  obtain ⟨st, pre, cur, post⟩ := x
  simp only at hpre
  subst hpre
  have hmain := simAll_round_left14 q b T hT tab s0 k hk hk1 st.val c st.isLt hc
    cur cq pre' post L hq m' s' h
  rw [enc_pre_last st pre' cq cur post L hq]
  rw [← enc_left_out m' pre' cq s' post L]
  exact hmain

namespace Reg

/-- 区域层面的一步：先按 `pick` 查表，再按方向把当前格挪进左/右列表。
    查表失败、或头已到区域尽头还要继续外移时返回 `none`
    （驱动机会在区域两端预置空白格，正常轮次不会触发后者）。 -/
def step {q : Nat} (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (c : Nat)
    (x : Reg q) : Option (Reg q) :=
  match pick (tab x.state x.cur) c with
  | none => none
  | some (m', s', d) =>
      match d with
      | Dir.stay => some { x with state := m', cur := s' }
      | Dir.right =>
          match x.post with
          | [] => none
          | p :: post' =>
              some { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
      | Dir.left =>
          match x.pre.reverse with
          | [] => none
          | cq :: rest =>
              some { state := m', pre := rest.reverse, cur := cq.1,
                     post := (s', false) :: x.post }

/-- 一步保持「所有格标记位为 0」。 -/
theorem step_markers {q : Nat} {tab : Fin q → Sym → List (Fin q × Sym × Dir)} {c : Nat}
    {x y : Reg q} (h : step tab c x = some y) (hx : x.MarkersOK) : y.MarkersOK := by
  cases hpick : pick (tab x.state x.cur) c with
  | none =>
      simp only [step, hpick] at h
      exact absurd h (by simp)
  | some v =>
      obtain ⟨m', s', d⟩ := v
      cases d with
      | stay =>
          simp only [step, hpick, Option.some.injEq] at h
          subst h
          exact hx
      | right =>
          cases hpost : x.post with
          | nil =>
              simp only [step, hpick, hpost] at h
              exact absurd h (by simp)
          | cons p post' =>
              simp only [step, hpick, hpost, Option.some.injEq] at h
              subst h
              refine ⟨?_, ?_⟩
              · intro q hq
                rcases List.mem_append.mp hq with h1 | h2
                · exact hx.1 q h1
                · simp only [List.mem_singleton] at h2
                  rw [h2]
              · intro q hq
                exact hx.2 q (by rw [hpost]; exact List.mem_cons_of_mem p hq)
      | left =>
          cases hpre : x.pre.reverse with
          | nil =>
              simp only [step, hpick, hpre] at h
              exact absurd h (by simp)
          | cons cq rest =>
              simp only [step, hpick, hpre, Option.some.injEq] at h
              subst h
              have hpre' : x.pre = rest.reverse ++ [cq] := by
                have := congrArg List.reverse hpre
                simpa [List.reverse_cons, List.reverse_reverse] using this
              refine ⟨?_, ?_⟩
              · intro q hq
                exact hx.1 q (by rw [hpre']; exact List.mem_append_left _ hq)
              · intro q hq
                rcases List.mem_cons.mp hq with h1 | h2
                · subst h1; rfl
                · exact hx.2 q h2

/-- 一步最多消耗掉左/右侧一个格：两侧长度各减少不超过 1。 -/
theorem step_len {q : Nat} {tab : Fin q → Sym → List (Fin q × Sym × Dir)} {c : Nat}
    {x y : Reg q} (h : step tab c x = some y) :
    x.pre.length ≤ y.pre.length + 1 ∧ x.post.length ≤ y.post.length + 1 := by
  cases hpick : pick (tab x.state x.cur) c with
  | none =>
      simp only [step, hpick] at h
      exact absurd h (by simp)
  | some v =>
      obtain ⟨m', s', d⟩ := v
      cases d with
      | stay =>
          simp only [step, hpick, Option.some.injEq] at h
          subst h
          exact ⟨Nat.le_add_right _ 1, Nat.le_add_right _ 1⟩
      | right =>
          cases hpost : x.post with
          | nil =>
              simp only [step, hpick, hpost] at h
              exact absurd h (by simp)
          | cons p post' =>
              simp only [step, hpick, hpost, Option.some.injEq] at h
              subst h
              refine ⟨?_, ?_⟩
              · change x.pre.length ≤ (x.pre ++ [(s', false)]).length + 1
                simp only [List.length_append, List.length_cons, List.length_nil]
                omega
              · change (p :: post').length ≤ post'.length + 1
                simp only [List.length_cons]
                omega
      | left =>
          cases hpre : x.pre.reverse with
          | nil =>
              simp only [step, hpick, hpre] at h
              exact absurd h (by simp)
          | cons cq rest =>
              simp only [step, hpick, hpre, Option.some.injEq] at h
              subst h
              have hpre' : x.pre = rest.reverse ++ [cq] := by
                have := congrArg List.reverse hpre
                simpa [List.reverse_cons, List.reverse_reverse] using this
              refine ⟨?_, ?_⟩
              · change x.pre.length ≤ rest.reverse.length + 1
                rw [hpre']
                simp only [List.length_append, List.length_cons, List.length_nil]
                omega
              · change x.post.length ≤ x.post.length + 1 + 1
                omega

end Reg

/-- 区域层面连续 `n` 轮的迭代（`none` 表示中途查表失败或走出区域）。 -/
def stepN {q : Nat} (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (c : Nat) :
    Nat → Reg q → Option (Reg q)
  | 0, x => some x
  | n + 1, x => (Reg.step tab c x).bind (stepN tab c n)

set_option maxHeartbeats 1000000 in
/-- 主归纳：`n` 轮之后，`simAll` 的纸带/状态正好是区域迭代 `stepN` 的结果。
    深度条件 `n ≤ pre.length`、`n ≤ post.length` 保证每一轮都不会走出区域。 -/
theorem simAll_run_steps (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (c : Nat) (hc : c < 2 ^ b) :
    ∀ (n k : Nat) (x y : Reg q) (L : List Sym) (hkn : k + n < T),
      x.MarkersOK → n ≤ x.pre.length → n ≤ x.post.length →
      stepN tab c n x = some y →
      (simAll q b T hT tab s0).run (14 * n)
        (Config.mk (embK q b T k (Nat.lt_of_le_of_lt (Nat.le_add_right k n) hkn)
          (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
          (x.enc L)) =
      Config.mk (embK q b T (k + n) hkn
        (codeState q b y.state.val c 0 0 y.state.isLt hc (by decide) (by decide)))
        (y.enc L) := by
  intro n
  induction n with
  | zero =>
      intro k x y L hkn hx hd1 hd2 h
      simp only [stepN, Option.some.injEq] at h
      subst h
      simp [DTM.run]
  | succ n ih =>
      intro k x y L hkn hx hd1 hd2 h
      simp only [stepN] at h
      cases hp : Reg.step tab c x with
      | none =>
          simp only [hp] at h
          exact absurd h (by simp)
      | some z =>
          simp only [hp, Option.bind] at h
          have hz_ok : z.MarkersOK := Reg.step_markers hp hx
          obtain ⟨hp1, hp2⟩ := Reg.step_len hp
          have hround : (simAll q b T hT tab s0).run 14
              (Config.mk (embK q b T k (by omega)
                (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
                (x.enc L)) =
              Config.mk (embK q b T (k + 1) (by omega)
                (codeState q b z.state.val c 0 0 z.state.isLt hc (by decide) (by decide)))
                (z.enc L) := by
            cases hpick : pick (tab x.state x.cur) c with
            | none =>
                rw [Reg.step, hpick] at hp
                exact absurd hp (by simp)
            | some v =>
                obtain ⟨m', s', d⟩ := v
                cases d with
                | stay =>
                    have hz : z = Reg.mk m' x.pre s' x.post := by
                      rw [Reg.step, hpick] at hp
                      exact (Option.some.inj hp).symm
                    subst hz
                    exact simAll_round_stay_enc q b T hT tab s0 k (by omega) (by omega)
                      c hc x L m' s' hpick
                | right =>
                    cases hpost : x.post with
                    | nil =>
                        rw [Reg.step, hpick, hpost] at hp
                        exact absurd hp (by simp)
                    | cons p post' =>
                        have hz : z = Reg.mk m' (x.pre ++ [(s', false)]) p.1 post' := by
                          rw [Reg.step, hpick, hpost] at hp
                          exact (Option.some.inj hp).symm
                        subst hz
                        exact simAll_round_right_enc q b T hT tab s0 k (by omega) (by omega)
                          c hc x L p post' (hx.2 p (by rw [hpost]; simp)) hpost m' s' hpick
                | left =>
                    cases hpre : x.pre.reverse with
                    | nil =>
                        rw [Reg.step, hpick, hpre] at hp
                        exact absurd hp (by simp)
                    | cons cq rest =>
                        have hz : z = Reg.mk m' rest.reverse cq.1 ((s', false) :: x.post) := by
                          rw [Reg.step, hpick, hpre] at hp
                          exact (Option.some.inj hp).symm
                        have hpre' : x.pre = rest.reverse ++ [cq] := by
                          have := congrArg List.reverse hpre
                          simpa [List.reverse_cons, List.reverse_reverse] using this
                        subst hz
                        exact simAll_round_left_enc q b T hT tab s0 k (by omega) (by omega)
                          c hc x L cq rest.reverse
                          (hx.1 cq (by rw [hpre']; simp)) (by simpa using hpre') m' s' hpick
          have hidx : k + (n + 1) = (k + 1) + n := by omega
          rw [show 14 * (n + 1) = 14 + 14 * n by omega, DTM.run_add, hround]
          simpa only [hidx] using
            ih (k + 1) z y L (by omega) hz_ok (by omega) (by omega) h








set_option maxHeartbeats 1000000 in
/-- 最后一轮（原地，`k + 1 = T`）：接受。 -/
theorem simAll_accept_stay_enc (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (hkT : k + 1 = T)
    (c : Nat) (hc : c < 2 ^ b) (x : Reg q) (L : List Sym)
    (m' : Fin q) (s' : Sym)
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.stay)) :
    (simAll q b T hT tab s0).run 14
      (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (x.enc L)) =
    Config.mk (⟨T * stateCount q b, by
      have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
      have := stateCount_pos q b hq; omega⟩ : Fin (T * stateCount q b + 2))
      (Reg.enc ({ state := m', pre := x.pre, cur := s', post := x.post } : Reg q) L) := by
  have h13 := simAll_round_stay q b T hT tab s0 k hk x.state.val c x.state.isLt hc x.cur x.pre x.post L m' s' h
  have hhalt : (simAll q b T hT tab s0).halted
      (Config.mk (embK q b T k hk
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)))
        (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells x.pre) ++ L)) ((some true) :: codeCells x.post))) = false := by
    have hh := simAll_halted_inner q b T hT tab s0 k
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)).isLt (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells x.pre) ++ L)) ((some true) :: codeCells x.post))
    simpa only [embK] using hh
  have hstep := simAll_step13_accept q b T hT tab s0 k m'.val c
    (symIdx s' * 3 + dirVal Dir.stay) hk hkT m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega)
    (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells x.pre) ++ L)) ((some true) :: codeCells x.post)) (by simp)
  -- 输入纸带的区域形式展开
  have hT0 : x.enc L =
      (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L)) ((some true) :: codeCells x.post)) := by
    simp only [Reg.enc]
  calc (simAll q b T hT tab s0).run 14
        (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (x.enc L))
      = (simAll q b T hT tab s0).run 14
          (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L)) ((some true) :: codeCells x.post))) := by
        rw [hT0]
    _ =  (simAll q b T hT tab s0).run 1
          ((simAll q b T hT tab s0).run 13
            (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L)) ((some true) :: codeCells x.post)))) := by
        rw [show (14 : Nat) = 13 + 1 by rfl, DTM.run_add]
    _ = (simAll q b T hT tab s0).run 1
          (Config.mk (embK q b T k hk
          (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.stay) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.stay; omega) (by decide)))
          (Tape.mk (codeSnd s' :: codeFst s' :: (List.reverse (codeCells x.pre) ++ L)) ((some true) :: codeCells x.post))) := by
        rw [h13]
    _ = Config.mk (⟨T * stateCount q b, by
      have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
      have := stateCount_pos q b hq; omega⟩ : Fin (T * stateCount q b + 2))
          (Reg.enc ({ state := m', pre := x.pre, cur := s', post := x.post } : Reg q) L) := by
        change (simAll q b T hT tab s0).run (0 + 1) _ = _
        rw [DTM.run_succ_of_not_halted _ 0 _ hhalt, hstep]
        simp only [DTM.run]
        simp only [Reg.enc]


set_option maxHeartbeats 1000000 in
/-- 最后一轮（右移，`k + 1 = T`）：接受。 -/
theorem simAll_accept_right_enc (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (hkT : k + 1 = T)
    (c : Nat) (hc : c < 2 ^ b) (x : Reg q) (L : List Sym)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (hp : p.2 = false)
    (hpost : x.post = p :: post')
    (m' : Fin q) (s' : Sym)
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.right)) :
    (simAll q b T hT tab s0).run 14
      (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (x.enc L)) =
    Config.mk (⟨T * stateCount q b, by
      have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
      have := stateCount_pos q b hq; omega⟩ : Fin (T * stateCount q b + 2))
      (Reg.enc ({ state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } : Reg q) L) := by
  have h13 := simAll_round_right q b T hT tab s0 k hk x.state.val c x.state.isLt hc x.cur p post' x.pre L hp m' s' h
  have hhalt : (simAll q b T hT tab s0).halted
      (Config.mk (embK q b T k hk
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)))
        (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells x.pre) ++ L)) ((some true) :: codeCells post'))) = false := by
    have hh := simAll_halted_inner q b T hT tab s0 k
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)).isLt (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells x.pre) ++ L)) ((some true) :: codeCells post'))
    simpa only [embK] using hh
  have hstep := simAll_step13_accept q b T hT tab s0 k m'.val c
    (symIdx s' * 3 + dirVal Dir.right) hk hkT m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega)
    (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells x.pre) ++ L)) ((some true) :: codeCells post')) (by simp)
  -- 输入纸带的区域形式展开
  have hT0 : x.enc L =
      (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L)) ((some true) :: codeCells (p :: post'))) := by
    simp only [Reg.enc, hpost]
  calc (simAll q b T hT tab s0).run 14
        (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (x.enc L))
      = (simAll q b T hT tab s0).run 14
          (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L)) ((some true) :: codeCells (p :: post')))) := by
        rw [hT0]
    _ =  (simAll q b T hT tab s0).run 1
          ((simAll q b T hT tab s0).run 13
            (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L)) ((some true) :: codeCells (p :: post'))))) := by
        rw [show (14 : Nat) = 13 + 1 by rfl, DTM.run_add]
    _ = (simAll q b T hT tab s0).run 1
          (Config.mk (embK q b T k hk
          (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.right) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.right; omega) (by decide)))
          (Tape.mk (codeSnd p.1 :: codeFst p.1 :: (some false) :: codeSnd s' :: codeFst s' :: (List.reverse (codeCells x.pre) ++ L)) ((some true) :: codeCells post'))) := by
        rw [h13]
    _ = Config.mk (⟨T * stateCount q b, by
      have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
      have := stateCount_pos q b hq; omega⟩ : Fin (T * stateCount q b + 2))
          (Reg.enc ({ state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } : Reg q) L) := by
        change (simAll q b T hT tab s0).run (0 + 1) _ = _
        rw [DTM.run_succ_of_not_halted _ 0 _ hhalt, hstep]
        simp only [DTM.run]
        rw [enc_pre_snoc m' x.pre p s' post' L]


set_option maxHeartbeats 1000000 in
/-- 最后一轮（左移，`k + 1 = T`）：接受。 -/
theorem simAll_accept_left_enc (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (hkT : k + 1 = T)
    (c : Nat) (hc : c < 2 ^ b) (x : Reg q) (L : List Sym)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (hq : cq.2 = false)
    (hpre : x.pre = pre' ++ [cq])
    (m' : Fin q) (s' : Sym)
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.left)) :
    (simAll q b T hT tab s0).run 14
      (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (x.enc L)) =
    Config.mk (⟨T * stateCount q b, by
      have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
      have := stateCount_pos q b hq; omega⟩ : Fin (T * stateCount q b + 2))
      (Reg.enc ({ state := m', pre := pre', cur := cq.1, post := (s', false) :: x.post } : Reg q) L) := by
  have h13 := simAll_round_left q b T hT tab s0 k hk x.state.val c x.state.isLt hc x.cur cq pre' x.post L hq m' s' h
  have hhalt : (simAll q b T hT tab s0).halted
      (Config.mk (embK q b T k hk
        (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)))
        (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeFst s' :: codeSnd s' :: (some false) :: codeCells x.post))) = false := by
    have hh := simAll_halted_inner q b T hT tab s0 k
      (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).val hk (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)).isLt (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeFst s' :: codeSnd s' :: (some false) :: codeCells x.post))
    simpa only [embK] using hh
  have hstep := simAll_step13_accept q b T hT tab s0 k m'.val c
    (symIdx s' * 3 + dirVal Dir.left) hk hkT m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega)
    (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeFst s' :: codeSnd s' :: (some false) :: codeCells x.post)) (by simp)
  -- 输入纸带的区域形式展开
  have hT0 : x.enc L =
      (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells x.post)) := by
    simp only [Reg.enc, hpre, codeCells, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, cellCode, symCode_eq, hq, List.reverse_append, List.reverse_cons,
      List.reverse_nil, List.nil_append, List.append_nil, List.cons_append,
      List.singleton_append, Bool.false_eq_true, ite_false]
  calc (simAll q b T hT tab s0).run 14
        (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (x.enc L))
      = (simAll q b T hT tab s0).run 14
          (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells x.post))) := by
        rw [hT0]
    _ =  (simAll q b T hT tab s0).run 1
          ((simAll q b T hT tab s0).run 13
            (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (some false) :: codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeCells x.post)))) := by
        rw [show (14 : Nat) = 13 + 1 by rfl, DTM.run_add]
    _ = (simAll q b T hT tab s0).run 1
          (Config.mk (embK q b T k hk
          (codeState q b m'.val c (symIdx s' * 3 + dirVal Dir.left) 13 m'.isLt hc (by have := symIdx_lt s'; have := dirVal_lt Dir.left; omega) (by decide)))
          (Tape.mk (codeSnd cq.1 :: codeFst cq.1 :: (List.reverse (codeCells pre') ++ L)) ((some true) :: codeFst s' :: codeSnd s' :: (some false) :: codeCells x.post))) := by
        rw [h13]
    _ = Config.mk (⟨T * stateCount q b, by
      have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
      have := stateCount_pos q b hq; omega⟩ : Fin (T * stateCount q b + 2))
          (Reg.enc ({ state := m', pre := pre', cur := cq.1, post := (s', false) :: x.post } : Reg q) L) := by
        change (simAll q b T hT tab s0).run (0 + 1) _ = _
        rw [DTM.run_succ_of_not_halted _ 0 _ hhalt, hstep]
        simp only [DTM.run]
        rw [enc_left_out m' pre' cq s' x.post L]

set_option maxHeartbeats 1000000 in
/-- 最后一轮（`k + 1 = T`）：`Reg.step` 成功就直接进入接受态。 -/
theorem simAll_final_accept (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (hkT : k + 1 = T)
    (c : Nat) (hc : c < 2 ^ b) (x y : Reg q) (L : List Sym)
    (hx : x.MarkersOK) (hd1 : 1 ≤ x.pre.length) (hd2 : 1 ≤ x.post.length)
    (h : Reg.step tab c x = some y) :
    (simAll q b T hT tab s0).run 14
      (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (x.enc L)) =
    Config.mk (⟨T * stateCount q b, by
      have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
      have := stateCount_pos q b hq; omega⟩ : Fin (T * stateCount q b + 2))
      (y.enc L) := by
  cases hpick : pick (tab x.state x.cur) c with
  | none =>
      rw [Reg.step, hpick] at h
      exact absurd h (by simp)
  | some v =>
      obtain ⟨m', s', d⟩ := v
      cases d with
      | stay =>
          have hy : y = Reg.mk m' x.pre s' x.post := by
            rw [Reg.step, hpick] at h
            exact (Option.some.inj h).symm
          subst hy
          exact simAll_accept_stay_enc q b T hT tab s0 k hk hkT c hc x L m' s' hpick
      | right =>
          cases hpost : x.post with
          | nil =>
              rw [hpost] at hd2
              simp at hd2
          | cons p post' =>
              have hy : y = Reg.mk m' (x.pre ++ [(s', false)]) p.1 post' := by
                rw [Reg.step, hpick, hpost] at h
                exact (Option.some.inj h).symm
              subst hy
              exact simAll_accept_right_enc q b T hT tab s0 k hk hkT c hc x L p post'
                (hx.2 p (by rw [hpost]; simp)) hpost m' s' hpick
      | left =>
          cases hpre : x.pre.reverse with
          | nil =>
              have hnil : x.pre = [] := by simpa using hpre
              rw [hnil] at hd1
              simp at hd1
          | cons cq rest =>
              have hy : y = Reg.mk m' rest.reverse cq.1 ((s', false) :: x.post) := by
                rw [Reg.step, hpick, hpre] at h
                exact (Option.some.inj h).symm
              have hpre' : x.pre = rest.reverse ++ [cq] := by
                have := congrArg List.reverse hpre
                simpa [List.reverse_cons, List.reverse_reverse] using this
              subst hy
              exact simAll_accept_left_enc q b T hT tab s0 k hk hkT c hc x L cq rest.reverse
                (hx.1 cq (by rw [hpre']; simp)) (by simpa using hpre') m' s' hpick

set_option maxHeartbeats 1000000 in
/-- 查表失败：5 步读到阶段 14，再用 1 步进入拒绝态（共 6 步）。 -/
theorem simAll_dead_reject (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (k : Nat) (hk : k < T) (c : Nat) (hc : c < 2 ^ b) (x : Reg q) (L : List Sym)
    (h : pick (tab x.state x.cur) c = none) :
    (simAll q b T hT tab s0).run 6
      (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (x.enc L)) =
    Config.mk (⟨T * stateCount q b + 1, by
      have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
      have := stateCount_pos q b hq; omega⟩ : Fin (T * stateCount q b + 2))
      (x.enc L) := by
  have h5 : (simAll q b T hT tab s0).run 5
      (Config.mk (embK q b T k hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (x.enc L)) =
      Config.mk (embK q b T k hk
        (codeState q b x.state.val c (symIdx x.cur) 14 x.state.isLt hc
          (by have := symIdx_lt x.cur; omega) (by decide)))
        (x.enc L) := by
    refine run_five_of_steps (simAll q b T hT tab s0)
      (c0 := Config.mk (embK q b T k hk
          (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
        (x.enc L))
      (c1 := Config.mk (embK q b T k hk
          (codeState q b x.state.val c 0 1 x.state.isLt hc (by decide) (by decide)))
        (Tape.mk (codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
          (codeSnd x.cur :: some true :: codeCells x.post)))
      (c2 := Config.mk (embK q b T k hk
          (codeState q b x.state.val c (symIdx (codeSnd x.cur)) 2 x.state.isLt hc
            (by have := symIdx_lt (codeSnd x.cur); omega) (by decide)))
        (Tape.mk (List.reverse (codeCells x.pre) ++ L)
          (codeFst x.cur :: codeSnd x.cur :: some true :: codeCells x.post)))
      (c3 := Config.mk (embK q b T k hk
          (codeState q b x.state.val c (symIdx x.cur) 3 x.state.isLt hc
            (by have := symIdx_lt x.cur; omega) (by decide)))
        (Tape.mk (codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
          (codeSnd x.cur :: some true :: codeCells x.post)))
      (c4 := Config.mk (embK q b T k hk
          (codeState q b x.state.val c (symIdx x.cur) 4 x.state.isLt hc
            (by have := symIdx_lt x.cur; omega) (by decide)))
        (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
          (some true :: codeCells x.post)))
      (c5 := Config.mk (embK q b T k hk
          (codeState q b x.state.val c (symIdx x.cur) 14 x.state.isLt hc
            (by have := symIdx_lt x.cur; omega) (by decide)))
        (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
          (some true :: codeCells x.post)))
        ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)).val hk
        (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)).isLt
        (x.enc L)
      simpa only [embK] using hh
    · have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b x.state.val c 0 1 x.state.isLt hc (by decide) (by decide)).val hk
        (codeState q b x.state.val c 0 1 x.state.isLt hc (by decide) (by decide)).isLt
        (Tape.mk (codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
        (codeSnd x.cur :: some true :: codeCells x.post))
      simpa only [embK] using hh
    · have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b x.state.val c (symIdx (codeSnd x.cur)) 2 x.state.isLt hc
        (by have := symIdx_lt (codeSnd x.cur); omega) (by decide)).val hk
        (codeState q b x.state.val c (symIdx (codeSnd x.cur)) 2 x.state.isLt hc
        (by have := symIdx_lt (codeSnd x.cur); omega) (by decide)).isLt
        (Tape.mk (List.reverse (codeCells x.pre) ++ L)
        (codeFst x.cur :: codeSnd x.cur :: some true :: codeCells x.post))
      simpa only [embK] using hh
    · have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b x.state.val c (symIdx x.cur) 3 x.state.isLt hc
        (by have := symIdx_lt x.cur; omega) (by decide)).val hk
        (codeState q b x.state.val c (symIdx x.cur) 3 x.state.isLt hc
        (by have := symIdx_lt x.cur; omega) (by decide)).isLt
        (Tape.mk (codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
        (codeSnd x.cur :: some true :: codeCells x.post))
      simpa only [embK] using hh
    · have hh := simAll_halted_inner q b T hT tab s0 k
        (codeState q b x.state.val c (symIdx x.cur) 4 x.state.isLt hc
        (by have := symIdx_lt x.cur; omega) (by decide)).val hk
        (codeState q b x.state.val c (symIdx x.cur) 4 x.state.isLt hc
        (by have := symIdx_lt x.cur; omega) (by decide)).isLt
        (Tape.mk (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L))
        (some true :: codeCells x.post))
      simpa only [embK] using hh
    · exact simAll_stepConfig_eq' q b T hT tab s0 k hk
        x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)
        (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L)) (codeCells x.post)
        ((some true)) (by decide) (by decide)
        (codeState q b x.state.val c 0 1 x.state.isLt hc (by decide) (by decide))
        ((some true)) Dir.left
        (simStep_stepC0 q b tab s0 x.state.val c x.state.isLt hc)
    · exact simAll_stepConfig_eq' q b T hT tab s0 k hk
        x.state.val c 0 1 x.state.isLt hc (by decide) (by decide)
        (codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L)) ((some true) :: codeCells x.post)
        (codeSnd x.cur) (by decide) (by decide)
        (codeState q b x.state.val c (symIdx (codeSnd x.cur)) 2 x.state.isLt hc
        (by have := symIdx_lt (codeSnd x.cur); omega) (by decide))
        (codeSnd x.cur) Dir.left
        (simStep_stepC1 q b tab s0 x.state.val c x.state.isLt hc x.cur x.cur Dir.stay)
    · exact simAll_stepConfig_eq' q b T hT tab s0 k hk
        x.state.val c (symIdx (codeSnd x.cur)) 2 x.state.isLt hc
        (by have := symIdx_lt (codeSnd x.cur); omega) (by decide)
        ((List.reverse (codeCells x.pre) ++ L)) (codeSnd x.cur :: (some true) :: codeCells x.post)
        (codeFst x.cur) (by decide) (by decide)
        (codeState q b x.state.val c (symIdx x.cur) 3 x.state.isLt hc
        (by have := symIdx_lt x.cur; omega) (by decide))
        (codeFst x.cur) Dir.right
        (simStep_stepC2 q b tab s0 x.state.val c x.state.isLt hc x.cur x.cur Dir.stay)
    · exact simAll_stepConfig_eq' q b T hT tab s0 k hk
        x.state.val c (symIdx x.cur) 3 x.state.isLt hc
        (by have := symIdx_lt x.cur; omega) (by decide)
        (codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L)) ((some true) :: codeCells x.post)
        (codeSnd x.cur) (by decide) (by decide)
        (codeState q b x.state.val c (symIdx x.cur) 4 x.state.isLt hc
        (by have := symIdx_lt x.cur; omega) (by decide))
        (codeSnd x.cur) Dir.right
        (simStep_stepC3 q b tab s0 x.state.val c x.state.isLt hc x.cur x.cur Dir.stay)
    · exact simAll_stepConfig_eq' q b T hT tab s0 k hk
        x.state.val c (symIdx x.cur) 4 x.state.isLt hc
        (by have := symIdx_lt x.cur; omega) (by decide)
        (codeSnd x.cur :: codeFst x.cur :: (List.reverse (codeCells x.pre) ++ L)) (codeCells x.post)
        ((some true)) (by decide) (by decide)
        (codeState q b x.state.val c (symIdx x.cur) 14 x.state.isLt hc
        (by have := symIdx_lt x.cur; omega) (by decide))
        ((some true)) Dir.stay
        (simStep_stepC4_none q b tab s0 x.state.val c x.state.isLt hc x.cur h)
  have hhalt5 : (simAll q b T hT tab s0).halted
      (Config.mk (embK q b T k hk
        (codeState q b x.state.val c (symIdx x.cur) 14 x.state.isLt hc
          (by have := symIdx_lt x.cur; omega) (by decide)))
        (x.enc L)) = false := by
    have hh := simAll_halted_inner q b T hT tab s0 k
      (codeState q b x.state.val c (symIdx x.cur) 14 x.state.isLt hc
        (by have := symIdx_lt x.cur; omega) (by decide)).val hk
      (codeState q b x.state.val c (symIdx x.cur) 14 x.state.isLt hc
        (by have := symIdx_lt x.cur; omega) (by decide)).isLt
      (x.enc L)
    simpa only [embK] using hh
  have hstep := simAll_step14_reject q b T hT tab s0 k x.state.val c (symIdx x.cur) hk
    x.state.isLt hc (by have := symIdx_lt x.cur; omega) (x.enc L) (by simp [Reg.enc])
  rw [show (6 : Nat) = 5 + 1 by rfl, DTM.run_add, h5]
  change (simAll q b T hT tab s0).run (0 + 1) _ = _
  rw [DTM.run_succ_of_not_halted _ 0 _ hhalt5, hstep]
  simp [DTM.run]

/-- `stepN` 保持「所有格标记位为 0」。 -/
theorem stepN_markers {q : Nat} {tab : Fin q → Sym → List (Fin q × Sym × Dir)} {c : Nat}
    {n : Nat} {x y : Reg q} (h : stepN tab c n x = some y) (hx : x.MarkersOK) :
    y.MarkersOK := by
  induction n generalizing x with
  | zero =>
      simp only [stepN, Option.some.injEq] at h
      subst h
      exact hx
  | succ n ih =>
      simp only [stepN] at h
      cases hp : Reg.step tab c x with
      | none => simp only [hp] at h; exact absurd h (by simp)
      | some z =>
          simp only [hp, Option.bind] at h
          exact ih h (Reg.step_markers hp hx)

/-- `stepN` 每轮最多消耗左/右侧一个格：长度减少不超过轮数。 -/
theorem stepN_len {q : Nat} {tab : Fin q → Sym → List (Fin q × Sym × Dir)} {c : Nat}
    {n : Nat} {x y : Reg q} (h : stepN tab c n x = some y) :
    x.pre.length ≤ y.pre.length + n ∧ x.post.length ≤ y.post.length + n := by
  induction n generalizing x with
  | zero =>
      simp only [stepN, Option.some.injEq] at h
      subst h
      exact ⟨by omega, by omega⟩
  | succ n ih =>
      simp only [stepN] at h
      cases hp : Reg.step tab c x with
      | none => simp only [hp] at h; exact absurd h (by simp)
      | some z =>
          simp only [hp, Option.bind] at h
          obtain ⟨h1, h2⟩ := Reg.step_len hp
          obtain ⟨h3, h4⟩ := ih h
          exact ⟨by omega, by omega⟩


set_option maxHeartbeats 1000000 in
/-- 完整运行：从第 `k` 轮首出发，若接下来 `n` 轮迭代都成功（`k + n = T`），
    则 `14 * n` 步后进入接受态。前提 `n ≤ pre.length`、`n ≤ post.length`
    保证每一轮都不会走出区域。 -/
theorem simAll_run_accept (q b T : Nat) (hT : 0 < T)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) (s0 : Fin q)
    (c : Nat) (hc : c < 2 ^ b) :
    ∀ (n k : Nat) (x y : Reg q) (L : List Sym) (hkn : k + n = T) (hn : 0 < n),
      x.MarkersOK → n ≤ x.pre.length → n ≤ x.post.length →
      stepN tab c n x = some y →
      (simAll q b T hT tab s0).run (14 * n)
        (Config.mk (embK q b T k (by omega)
          (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
          (x.enc L)) =
      Config.mk (⟨T * stateCount q b, by
        have hq : 0 < q := Nat.lt_of_le_of_lt (Nat.zero_le _) s0.isLt
        have := stateCount_pos q b hq; omega⟩ : Fin (T * stateCount q b + 2))
        (y.enc L) := by
  intro n
  induction n with
  | zero =>
      intro k x y L hkn hn
      exact absurd hn (by omega)
  | succ n ih =>
      intro k x y L hkn hn hx hd1 hd2 h
      simp only [stepN] at h
      cases hstep : Reg.step tab c x with
      | none =>
          simp only [hstep] at h
          exact absurd h (by simp)
      | some z =>
          simp only [hstep, Option.bind] at h
          have hz_ok : z.MarkersOK := Reg.step_markers hstep hx
          obtain ⟨hs1, hs2⟩ := Reg.step_len hstep
          by_cases hn0 : n = 0
          · -- 最后一轮：直接接受
            subst hn0
            simp only [stepN, Option.some.injEq] at h
            subst h
            have hkT : k + 1 = T := by omega
            exact simAll_final_accept q b T hT tab s0 k (by omega) hkT c hc x z L hx
              (by omega) (by omega) hstep
          · -- 还有多于一轮：先走一轮（重启），再归纳
            have hk1 : k + 1 < T := by omega
            have hround : (simAll q b T hT tab s0).run 14
                (Config.mk (embK q b T k (by omega)
                  (codeState q b x.state.val c 0 0 x.state.isLt hc (by decide) (by decide)))
                  (x.enc L)) =
                Config.mk (embK q b T (k + 1) (by omega)
                  (codeState q b z.state.val c 0 0 z.state.isLt hc (by decide) (by decide)))
                  (z.enc L) := by
              cases hpick : pick (tab x.state x.cur) c with
              | none =>
                  rw [Reg.step, hpick] at hstep
                  exact absurd hstep (by simp)
              | some v =>
                  obtain ⟨m', s', d⟩ := v
                  cases d with
                  | stay =>
                      have hz : z = Reg.mk m' x.pre s' x.post := by
                        rw [Reg.step, hpick] at hstep
                        exact (Option.some.inj hstep).symm
                      subst hz
                      exact simAll_round_stay_enc q b T hT tab s0 k (by omega) (by omega)
                        c hc x L m' s' hpick
                  | right =>
                      cases hpost : x.post with
                      | nil =>
                          rw [Reg.step, hpick, hpost] at hstep
                          exact absurd hstep (by simp)
                      | cons p post' =>
                          have hz : z = Reg.mk m' (x.pre ++ [(s', false)]) p.1 post' := by
                            rw [Reg.step, hpick, hpost] at hstep
                            exact (Option.some.inj hstep).symm
                          subst hz
                          exact simAll_round_right_enc q b T hT tab s0 k (by omega) (by omega)
                            c hc x L p post' (hx.2 p (by rw [hpost]; simp)) hpost m' s' hpick
                  | left =>
                      cases hpre : x.pre.reverse with
                      | nil =>
                          rw [Reg.step, hpick, hpre] at hstep
                          exact absurd hstep (by simp)
                      | cons cq rest =>
                          have hz : z = Reg.mk m' rest.reverse cq.1 ((s', false) :: x.post) := by
                            rw [Reg.step, hpick, hpre] at hstep
                            exact (Option.some.inj hstep).symm
                          have hpre' : x.pre = rest.reverse ++ [cq] := by
                            have := congrArg List.reverse hpre
                            simpa [List.reverse_cons, List.reverse_reverse] using this
                          subst hz
                          exact simAll_round_left_enc q b T hT tab s0 k (by omega) (by omega)
                            c hc x L cq rest.reverse
                            (hx.1 cq (by rw [hpre']; simp)) (by simpa using hpre') m' s' hpick
            have hidx : k + (n + 1) = (k + 1) + n := by omega
            have hkn' : (k + 1) + n = T := by omega
            rw [show 14 * (n + 1) = 14 + 14 * n by omega, DTM.run_add, hround]
            simpa only [hidx] using
              ih (k + 1) z y L hkn' (by omega) hz_ok (by omega) (by omega) h


/-- 区域对应的被模拟格局：左侧为 `pre` 的逆序，右侧为 `cur` 后接 `post`。 -/
def Reg.toConfig {q : Nat} (x : Reg q) : Config q :=
  { state := x.state,
    tape := Tape.mk (x.pre.reverse.map Prod.fst) (x.cur :: x.post.map Prod.fst) }

/-- 区域的格表（含头标记）：`pre` + 当前格（标记 1）+ `post`。 -/
def Reg.cells {q : Nat} (x : Reg q) : List (Sym × Bool) :=
  x.pre ++ [(x.cur, true)] ++ x.post

/-- 标记位全 0 的格表，映射 `(·.1, false)` 不改变列表。 -/
theorem map_fst_false_eq_self (l : List (Sym × Bool)) (h : ∀ p ∈ l, p.2 = false) :
    l.map (fun p => (p.1, false)) = l := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
      have hp : p.2 = false := h p (by simp)
      have hps : ∀ q ∈ ps, q.2 = false := fun q hq => h q (by simp [hq])
      simp only [List.map_cons]
      rw [ih hps]
      cases p with
      | mk a b =>
          simp only [Prod.snd] at hp
          rw [hp]

/-- 区域对应的格局，其格表正好是 `Reg.cells`。 -/
theorem cellsOfTape_toConfig {q : Nat} (x : Reg q) (hx : x.MarkersOK) :
    Tape.cellsOfTape x.toConfig.tape = x.cells := by
  simp only [Tape.cellsOfTape, Reg.cells, Reg.toConfig, List.map_cons, List.map_reverse,
    List.map_map, Function.comp_def, List.singleton_append, List.reverse_reverse]

  rw [map_fst_false_eq_self x.pre hx.1, map_fst_false_eq_self x.post hx.2,
    List.append_assoc, List.singleton_append]

/-- 区域一步与 NTM 一步一致（原地移动）。 -/
theorem stepWith_stay {q : Nat} (M : NTM q) (x : Reg q) (c : Nat)
    (m' : Fin q) (s' : Sym)
    (h : pick (M.step x.state x.cur) c = some (m', s', Dir.stay)) :
    M.stepWith x.toConfig c = some (Reg.mk m' x.pre s' x.post).toConfig := by
  unfold NTM.stepWith
  simp only [Reg.toConfig, Tape.read, List.headD]
  rw [h]
  simp only [Tape.write, Tape.move, List.tail]

/-- 区域一步与 NTM 一步一致（右移；要求右邻格存在）。 -/
theorem stepWith_right {q : Nat} (M : NTM q) (x : Reg q) (c : Nat)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (hp : p.2 = false)
    (hpost : x.post = p :: post')
    (m' : Fin q) (s' : Sym)
    (h : pick (M.step x.state x.cur) c = some (m', s', Dir.right)) :
    M.stepWith x.toConfig c =
      some (Reg.mk m' (x.pre ++ [(s', false)]) p.1 post').toConfig := by
  unfold NTM.stepWith
  simp only [Reg.toConfig, Tape.read, List.headD]
  rw [h]
  simp only [Tape.write, Tape.move, Tape.moveRight, List.tail, hpost, List.map_cons,
    List.map_reverse, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.singleton_append]

/-- 区域一步与 NTM 一步一致（左移；要求左邻格存在）。 -/
theorem stepWith_left {q : Nat} (M : NTM q) (x : Reg q) (c : Nat)
    (cq : Sym × Bool) (pre' : List (Sym × Bool)) (hq : cq.2 = false)
    (hpre : x.pre = pre' ++ [cq])
    (m' : Fin q) (s' : Sym)
    (h : pick (M.step x.state x.cur) c = some (m', s', Dir.left)) :
    M.stepWith x.toConfig c =
      some (Reg.mk m' pre' cq.1 ((s', false) :: x.post)).toConfig := by
  unfold NTM.stepWith
  simp only [Reg.toConfig, Tape.read, List.headD]
  rw [h]
  simp only [Tape.write, Tape.move, Tape.moveLeft, List.tail, hpre, List.map_cons,
    List.map_reverse, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.cons_append, List.singleton_append]

/-- 区域一步与 NTM 一步一致（分派）。 -/
theorem stepWith_of_step {q : Nat} (M : NTM q) (x y : Reg q) (c : Nat)
    (hx : x.MarkersOK) (h : Reg.step M.step c x = some y) :
    M.stepWith x.toConfig c = some y.toConfig := by
  cases hpick : pick (M.step x.state x.cur) c with
  | none =>
      rw [Reg.step, hpick] at h
      exact absurd h (by simp)
  | some v =>
      obtain ⟨m', s', d⟩ := v
      cases d with
      | stay =>
          have hy : y = Reg.mk m' x.pre s' x.post := by
            rw [Reg.step, hpick] at h
            exact (Option.some.inj h).symm
          subst hy
          exact stepWith_stay M x c m' s' hpick
      | right =>
          cases hpost : x.post with
          | nil =>
              rw [Reg.step, hpick, hpost] at h
              exact absurd h (by simp)
          | cons p post' =>
              have hy : y = Reg.mk m' (x.pre ++ [(s', false)]) p.1 post' := by
                rw [Reg.step, hpick, hpost] at h
                exact (Option.some.inj h).symm
              subst hy
              exact stepWith_right M x c p post' (hx.2 p (by rw [hpost]; simp)) hpost m' s' hpick
      | left =>
          cases hpre : x.pre.reverse with
          | nil =>
              rw [Reg.step, hpick, hpre] at h
              exact absurd h (by simp)
          | cons cq rest =>
              have hy : y = Reg.mk m' rest.reverse cq.1 ((s', false) :: x.post) := by
                rw [Reg.step, hpick, hpre] at h
                exact (Option.some.inj h).symm
              have hpre' : x.pre = rest.reverse ++ [cq] := by
                have := congrArg List.reverse hpre
                simpa [List.reverse_cons, List.reverse_reverse] using this
              subst hy
              exact stepWith_left M x c cq rest.reverse
                (hx.1 cq (by rw [hpre']; simp)) (by simpa using hpre') m' s' hpick

/-- 按选择列表逐轮迭代区域；语义与 `NTM.runWith` 对齐：
    已停机则原地返回，剩余选择用尽而仍未停机则 `none`。 -/
def stepNs {q : Nat} (M : NTM q) : Nat → List Nat → Reg q → Option (Reg q)
  | 0, _, x => some x
  | n + 1, [], x =>
      match M.halted x.toConfig with
      | true => some x
      | false => none
  | n + 1, c :: cs, x =>
      match M.halted x.toConfig with
      | true => some x
      | false => (Reg.step M.step c x).bind (stepNs M n cs)

/-- 区域迭代成功 ⇒ 对应的 NTM 运行成功（区域不越界的前提下）。 -/
theorem runWith_of_stepNs {q : Nat} (M : NTM q) :
    ∀ (n : Nat) (cs : List Nat) (x y : Reg q),
      x.MarkersOK → n ≤ x.pre.length → n ≤ x.post.length →
      stepNs M n cs x = some y →
      M.runWith n cs x.toConfig = some y.toConfig := by
  intro n
  induction n with
  | zero =>
      intro cs x y _ _ _ h
      simp only [stepNs, Option.some.injEq] at h
      subst h
      rfl
  | succ n ih =>
      intro cs x y hx hd1 hd2 h
      cases cs with
      | nil =>
          by_cases hh : M.halted x.toConfig = true
          · simp only [stepNs, hh] at h
            simp only [Option.some.injEq] at h
            subst h
            rw [NTM.runWith_succ]
            simp only [hh]
          · simp only [stepNs, hh] at h
            exact absurd h (by simp)
      | cons c cs =>
          by_cases hh : M.halted x.toConfig = true
          · simp only [stepNs, hh] at h
            simp only [Option.some.injEq] at h
            subst h
            rw [NTM.runWith_succ]
            simp only [hh]
          · simp only [stepNs, hh] at h
            cases hs : Reg.step M.step c x with
            | none =>
                rw [hs] at h
                exact absurd h (by simp)
            | some z =>
                rw [hs, Option.bind_some] at h
                have hz := stepWith_of_step M x z c hx hs
                have hzok : z.MarkersOK := Reg.step_markers hs hx
                obtain ⟨hz1, hz2⟩ := Reg.step_len hs
                rw [NTM.runWith_succ]
                simp only [hh, hz]
                exact ih cs z y hzok (by omega) (by omega) h

/-- 区域一步的反向：`stepWith` 成功且两端都有格时，`Reg.step` 也成功，
    且结果正是 `stepWith` 结果的区域表示。 -/
theorem exists_step_of_stepWith {q : Nat} (M : NTM q) (x : Reg q) (c : Nat)
    (hx : x.MarkersOK) (hpre : x.pre ≠ []) (hpost : x.post ≠ []) (y : Config q)
    (h : M.stepWith x.toConfig c = some y) :
    ∃ z : Reg q, Reg.step M.step c x = some z ∧ y = z.toConfig := by
  cases hpick : pick (M.step x.state x.cur) c with
  | none =>
      unfold NTM.stepWith at h
      simp only [Reg.toConfig, Tape.read, List.headD] at h
      rw [hpick] at h
      exact absurd h (by simp)
  | some v =>
      obtain ⟨m', s', d⟩ := v
      cases d with
      | stay =>
          refine ⟨Reg.mk m' x.pre s' x.post, ?_, ?_⟩
          · rw [Reg.step, hpick]
          · rw [stepWith_stay M x c m' s' hpick] at h
            exact (Option.some.inj h).symm
      | right =>
          obtain ⟨p, post', hpost'⟩ := List.exists_cons_of_ne_nil hpost
          refine ⟨Reg.mk m' (x.pre ++ [(s', false)]) p.1 post', ?_, ?_⟩
          · rw [Reg.step, hpick, hpost']
          · rw [stepWith_right M x c p post'
              (hx.2 p (by rw [hpost']; simp)) hpost' m' s' hpick] at h
            exact (Option.some.inj h).symm
      | left =>
          obtain ⟨cq, rest, hpre'⟩ := List.exists_cons_of_ne_nil (show x.pre.reverse ≠ [] from by
            intro hnil
            have : x.pre = [] := by simpa using hnil
            exact hpre this)
          have hqeq : x.pre = rest.reverse ++ [cq] := by
            have := congrArg List.reverse hpre'
            simpa [List.reverse_cons, List.reverse_reverse] using this
          refine ⟨Reg.mk m' rest.reverse cq.1 ((s', false) :: x.post), ?_, ?_⟩
          · rw [Reg.step, hpick, hpre']
          · rw [stepWith_left M x c cq rest.reverse
              (hx.1 cq (by rw [hqeq]; simp)) hqeq m' s' hpick] at h
            exact (Option.some.inj h).symm

/-- 区域迭代在某个接受态停机 ⇒ NTM 在 T 步内接受（驱动器正确性的“可靠”方向）。 -/
theorem acceptsWithin_of_stepNs_accept {q : Nat} (M : NTM q) {n T : Nat} {cs : List Nat}
    {x y : Reg q} {w : List Bool}
    (hx : x.MarkersOK) (hd1 : n ≤ x.pre.length) (hd2 : n ≤ x.post.length)
    (hxw : CfgEquiv x.toConfig (M.init w)) (hcs : cs.length ≤ T) (hnT : n ≤ T)
    (h : stepNs M n cs x = some y) (hacc : y.state = M.accept) :
    M.AcceptsWithin w T := by
  have hrun := runWith_of_stepNs M n cs x y hx hd1 hd2 h
  have hhalt : M.halted y.toConfig = true := by
    have h1 : y.toConfig.state = M.accept := hacc
    exact NTM.halted_of_state M y.toConfig (Or.inl h1)
  have hrun' := NTM.runWith_extend M n cs x.toConfig y.toConfig hrun hhalt T []
    (by omega)
  -- 空白预留不改变接受语义：把区域侧运行搬到 `M.init w` 侧
  refine NTM.acceptsWithin_of_sameInfS M w T x.toConfig hxw.1 hxw.2
    ⟨cs ++ [], ?_, y.toConfig, hrun', hacc⟩
  simp only [List.length_append, List.length_nil]
  omega

/-- 完备性方向：若 NTM 有一条接受运行，则区域迭代在某个接受态停机
    （驱动器能“找到”接受分支）。 -/
theorem exists_accept_of_runWith {q : Nat} (M : NTM q) :
    ∀ (n : Nat) (cs : List Nat) (x : Reg q) (y : Config q),
      x.MarkersOK → n ≤ x.pre.length → n ≤ x.post.length →
      M.runWith n cs x.toConfig = some y → y.state = M.accept →
      ∃ (t : Nat) (cs' : List Nat) (z : Reg q),
        t ≤ n ∧ cs'.length ≤ t ∧ stepNs M t cs' x = some z ∧
          z.state = M.accept ∧ z.toConfig = y := by
  intro n
  induction n with
  | zero =>
      intro cs x y hx hd1 hd2 h hacc
      simp only [NTM.runWith, Option.some.injEq] at h
      subst h
      exact ⟨0, [], x, by omega, by simp, rfl, hacc, rfl⟩
  | succ n ih =>
      intro cs x y hx hd1 hd2 h hacc
      rw [NTM.runWith_succ] at h
      cases hh : M.halted x.toConfig with
      | true =>
          simp only [hh, Option.some.injEq] at h
          subst h
          exact ⟨0, [], x, by omega, by simp, rfl, hacc, rfl⟩
      | false =>
          simp only [hh] at h
          cases cs with
          | nil => cases h
          | cons c cs =>
              cases hstep : M.stepWith x.toConfig c with
              | none =>
                  simp only [hstep] at h
                  cases h
              | some c1 =>
                  simp only [hstep, Option.bind_some] at h
                  have hpre : x.pre ≠ [] := by
                    intro hnil
                    rw [hnil] at hd1
                    simp at hd1
                  have hpost : x.post ≠ [] := by
                    intro hnil
                    rw [hnil] at hd2
                    simp at hd2
                  obtain ⟨z, hzstep, hzc⟩ :=
                    exists_step_of_stepWith M x c hx hpre hpost c1 hstep
                  have hzok : z.MarkersOK := Reg.step_markers hzstep hx
                  obtain ⟨hz1, hz2⟩ := Reg.step_len hzstep
                  have hrun' : M.runWith n cs z.toConfig = some y := by
                    rw [← hzc]
                    exact h
                  obtain ⟨t, cs', z', htn, hlen, hit, hacc', hzy⟩ :=
                    ih cs z y hzok (by omega) (by omega) hrun' hacc
                  refine ⟨t + 1, c :: cs', z', by omega, ?_, ?_, hacc', hzy⟩
                  · simp only [List.length_cons]
                    omega
                  · simp only [stepNs, hh, hzstep, Option.bind_some]
                    exact hit

/-- `seekMark` 在区域编码上的结果正是 `Reg.enc`：找头标记组件与区域表示对齐。 -/
theorem seekMark_run_enc {q : Nat} (st : Fin q) (pre : List (Sym × Bool))
    (h : ∀ p ∈ pre, p.2 = false) (s : Sym) (post : List (Sym × Bool)) (L : List Sym) :
    seekMark.run (3 * pre.length + 3)
      (Config.mk (0 : Fin 4)
        (Tape.mk L (codeCells pre ++ cellCode (s, true) ++ codeCells post))) =
    Config.mk (3 : Fin 4) ((Reg.mk st pre s post).enc L) := by
  rw [seekMark_run pre h s post L]
  congr 1
  simp only [Reg.enc, Reg.mk, symCode_eq, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, List.append_assoc]

/-- 暴力搜索成功 ⇒ 区域迭代在某个接受态停机（驱动器的规格接口）：
    由 `bruteForce_eq_true_iff` + 索引版接受语义 + `exists_accept_of_runWith` 合成。 -/
theorem exists_stepNs_accept_of_bruteForce {q : Nat} (M : NTM q) {B T : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (x : Reg q) (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hd1 : T ≤ x.pre.length) (hd2 : T ≤ x.post.length)
    (h : M.bruteForce B T w = true) :
    ∃ (t : Nat) (cs : List Nat) (z : Reg q),
      t ≤ T ∧ cs.length ≤ t ∧ stepNs M t cs x = some z ∧ z.state = M.accept := by
  have hacc : M.AcceptsWithin w T :=
    (M.bruteForce_eq_true_iff hB hBpos w T).mp h
  obtain ⟨i, hi, c, hrun, hcst⟩ :=
    (acceptsWithin_iff_exists_index hB hBpos w T).mp hacc
  -- 空白预留不改变运行：把 `M.init w` 侧的成功运行搬到区域侧
  obtain ⟨c2, hrunx, hst⟩ :=
    NTM.runWith_cfgEquiv M T (seqOfIndex B T i) hxw.symm c hrun
  have hcst2 : c2.state = M.accept := by rw [← hst]; exact hcst
  obtain ⟨t, cs', z, htT, hlen, hit, hacc', _⟩ :=
    exists_accept_of_runWith M T (seqOfIndex B T i) x c2 hx hd1 hd2 hrunx hcst2
  exact ⟨t, cs', z, htT, hlen, hit, hacc'⟩

/-- 反向：区域迭代停在接受态 ⇒ 暴力搜索成功（驱动器规格的另一半）。 -/
theorem bruteForce_of_stepNs_accept {q : Nat} (M : NTM q) {B T t : Nat}
    {cs : List Nat} {x z : Reg q} {w : List Bool}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (hx : x.MarkersOK) (hd1 : t ≤ x.pre.length) (hd2 : t ≤ x.post.length)
    (hxw : CfgEquiv x.toConfig (M.init w)) (hlen : cs.length ≤ T) (ht : t ≤ T)
    (h : stepNs M t cs x = some z) (hacc : z.state = M.accept) :
    M.bruteForce B T w = true := by
  have hrun := runWith_of_stepNs M t cs x z hx hd1 hd2 h
  have hhalt : M.halted z.toConfig = true :=
    NTM.halted_of_state M z.toConfig (Or.inl hacc)
  have hrun' := NTM.runWith_extend M t cs x.toConfig z.toConfig hrun hhalt T []
    (by omega)
  have haccW : M.AcceptsWithin w T :=
    NTM.acceptsWithin_of_sameInfS M w T x.toConfig hxw.1 hxw.2
      ⟨cs ++ [], by simp only [List.length_append, List.length_nil]; omega,
        z.toConfig, hrun', hacc⟩
  exact (M.bruteForce_eq_true_iff hB hBpos w T).mpr haccW

/-- **分支搜索语义接口（双向合一）**：暴力搜索成功 ⇔ 存在一条「区域迭代在 ≤T 步内
    停在接受态」的选支序列。合成 `exists_stepNs_accept_of_bruteForce` 与
    `bruteForce_of_stepNs_accept`，供外层枚举机对齐。
    Unified branch-search interface: brute force succeeds iff some choice sequence drives
    the region iteration to an accepting state within ≤T steps. -/
theorem bruteForce_iff_exists_stepNs_accept {q : Nat} (M : NTM q) {B T : Nat}
    (hB : ∀ s a, (M.step s a).length ≤ B) (hBpos : 0 < B)
    (w : List Bool) (x : Reg q) (hx : x.MarkersOK) (hxw : CfgEquiv x.toConfig (M.init w))
    (hd1 : T ≤ x.pre.length) (hd2 : T ≤ x.post.length) :
    M.bruteForce B T w = true ↔
      ∃ (t : Nat) (cs : List Nat) (z : Reg q),
        t ≤ T ∧ cs.length ≤ t ∧ stepNs M t cs x = some z ∧ z.state = M.accept := by
  constructor
  · intro h
    exact exists_stepNs_accept_of_bruteForce M hB hBpos w x hx hxw hd1 hd2 h
  · rintro ⟨t, cs, z, htT, hlen, hit, hacc⟩
    exact bruteForce_of_stepNs_accept M hB hBpos hx (by omega) (by omega) hxw
      (by omega) htT hit hacc

end DTM

end Pnp
