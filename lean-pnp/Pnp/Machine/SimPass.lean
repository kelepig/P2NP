/-
  文件：Pnp/Machine/SimPass.lean
  File: Pnp/Machine/SimPass.lean

  主题：把「完整一轮」`simDrive_roundFull_*` 组合成一次完整的分支通路（多轮），
  并定义数字区（unary 块序列）的列表表示。
  Topic: compose full rounds into one branch pass and define the unary digit-area
  list representation.

  数字区（左侧列表顺序，从模拟区往外）：每块写成 `0 1^(k+2)`，其中块值 `k`
  表示下一轮的选择编号为 `k + 1`；块序列末尾接一个左边界空白。
  Digit area (left-list order, away from the simulation region): each block is
  `0 1^(k+2)`; block value `k` means the next round's choice index is `k + 1`;
  the area ends with the left-boundary blank.

  本文件给出：
    - `digitArea` 与头部/非空引理；
    - `PassRes`（一次通路的步数、数字区零计数、计数器、终态区域）；
    - 三个方向的单轮耗时常量 `roundCost*` 与单轮规范形引理 `simDrive_roundCanon_*`；
    - `passRun`（通路驱动器的语义递归）与主定理 `simDrive_pass`。
  This file provides the digit-area encoding, the pass result record, per-round cost
  constants with canonical-form lemmas, the semantic pass driver `passRun`, and the
  main theorem `simDrive_pass`.
-/

import Pnp.Machine.SimRound

set_option maxHeartbeats 2000000

namespace Pnp

namespace DTM

/-- 数字区（左侧列表顺序）：`digitArea ks` 是各块的拼接，末尾一个左边界空白。
    每块 `k` 写成 `0 1^(k+2)`。
    Digit area in left-list order: blocks `0 1^(k+2)` concatenated, then one
    left-boundary blank. -/
def digitArea : List Nat → List Sym
  | [] => [none]
  | k :: ks => some false :: (some true :: (List.replicate (k + 1) (some true) ++ digitArea ks))

/-- 数字区非空。`digitArea` is never empty. -/
theorem digitArea_ne_nil (ks : List Nat) : digitArea ks ≠ [] := by
  cases ks with
  | nil => simp [digitArea]
  | cons k ks => simp [digitArea]

/-- 数字区的首符号不是 1（是 0 或左边界空白）。
    The head of the digit area is not a `1` symbol. -/
theorem digitArea_head_ne_true (ks : List Nat) (y : Sym) (ys : List Sym)
    (h : digitArea ks = y :: ys) : y ≠ some true := by
  rintro rfl
  cases ks with
  | nil => simp [digitArea] at h
  | cons k ks => simp [digitArea] at h

/-- 一次通路的结果：累计步数、数字区零计数、计数器（含界证明）、终态区域。
    Result of one branch pass: accumulated steps, zero count of the digit area,
    the counter (with its bound proof), and the final region. -/
structure PassRes (q b : Nat) where
  /-- 累计步数。 -/
  steps : Nat
  /-- 数字区里已擦成 0 的格数（紧跟分隔空白之后）。 -/
  z : Nat
  /-- 终态计数器（= 下一轮的选择编号）。 -/
  c : Nat
  /-- 计数器合法（`c < 2^b`）。 -/
  hc : c < 2 ^ b
  /-- 终态区域。 -/
  reg : Reg q

/-- 起点格局（模拟层相位 0）：区域编码后接 `0^Z` 与剩余数字区。
    Start configuration (simulation layer, phase 0): region encoding followed by
    `0^Z` and the remaining digit area. -/
def passStart {q b : Nat} (x : Reg q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (Z : Nat) (ks : List Nat) : Config (stateCountD q b) :=
  Config.mk (embS (codeState q b m c 0 0 hm hc (by decide) (by decide)))
    (x.enc (none :: List.replicate Z (some false) ++ digitArea ks))

/-- 终点格局（模拟层相位 0）：区域编码后接 `0^Z` 与空数字区（只剩左边界空白）。
    End configuration (simulation layer, phase 0): region encoding followed by
    `0^Z` and the empty digit area (only the left-boundary blank). -/
def passEnd {q b : Nat} (r : PassRes q b) : Config (stateCountD q b) :=
  Config.mk (embS (codeState q b r.reg.state.val r.c 0 0 r.reg.state.isLt r.hc
      (by decide) (by decide)))
    (r.reg.enc (none :: List.replicate r.z (some false) ++ digitArea []))

/-- 一轮（原地 / stay）的精确步数。Cost of one stay round. -/
def roundCostStay {q : Nat} (x : Reg q) (z k : Nat) (s' : Sym) : Nat :=
  (14 + ((codeFst s' :: List.reverse (codeCells x.pre)).length + 2) + (z + k + 3))
    + ((1 + ((List.replicate (k + 1) (some true)
      ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
      + (3 * x.pre.length + 3 + 1))

/-- 一轮（右移 / right）的精确步数。Cost of one right round. -/
def roundCostRight {q : Nat} (x : Reg q) (z k : Nat) (p : Sym × Bool) (s' : Sym) : Nat :=
  (14 + ((codeFst p.1
      :: List.reverse (codeCells (x.pre ++ [(s', false)]))).length + 2) + (z + k + 3))
    + ((1 + ((List.replicate (k + 1) (some true)
      ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
      + (3 * (x.pre ++ [(s', false)]).length + 3 + 1))

/-- 一轮（左移 / left）的精确步数。Cost of one left round. -/
def roundCostLeft {q : Nat} (z k : Nat) (pre' : List (Sym × Bool))
    (cq : Sym × Bool) (s' : Sym) : Nat :=
  (14 + ((codeFst cq.1 :: List.reverse (codeCells pre')).length + 2) + (z + k + 3))
    + ((1 + ((List.replicate (k + 1) (some true)
      ++ (some true :: List.replicate (z + 1) (some false))).length + 1))
      + (3 * pre'.length + 3 + 1))

/-- 物理纸带左列表与 `Reg.enc` 的同一性：`reverse (codeCells pre ++ symCode cur)` 就是
    `Reg.enc` 左列表的头部。Region-encoding tape equality helper. -/
theorem tape_eq_enc {q : Nat} (x : Reg q) (L : List Sym) :
    Tape.mk (List.reverse (codeCells x.pre ++ symCode x.cur) ++ L)
        (some true :: codeCells x.post) = x.enc L := by
  simp only [Reg.enc, symCode_eq, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.append_assoc, List.cons_append]

/-- 数字区擦除段的长度：`|1^(k+1) ++ 1 :: 0^(z+1)| = z + k + 3`。
    Length of the erase segment in one round. -/
theorem eraseLen (z k : Nat) :
    (List.replicate (k + 1) (some true)
      ++ (some true :: List.replicate (z + 1) (some false))).length = z + k + 3 := by
  simp only [List.length_append, List.length_replicate, List.length_cons]
  omega

/-- **单轮规范形（原地 / stay）**：从 `passStart` 出发跑完一轮，回到 `passStart`，
    零计数增加 `k + 3`，计数器变为 `K - 1`，区域更新。
    Canonical stay round: `passStart` to `passStart`, zeros grow by `k + 3`,
    the counter becomes `K - 1`. -/
theorem simDrive_roundCanon_stay (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (hpre : ∀ p ∈ x.pre, p.2 = false)
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.stay))
    (ks : List Nat) (htail : digitArea ks = xc :: X') :
    (simDrive q b tab s0).run (roundCostStay x z k s')
      (passStart x m c hm hc z (k :: ks)) =
    passStart ({ state := m', pre := x.pre, cur := s', post := x.post } : Reg q)
      m'.val (K - 1) m'.isLt (by omega) (z + k + 3) ks := by
  have hstart : none :: List.replicate z (some false) ++ digitArea (k :: ks) =
      none :: some false :: (List.replicate z (some false)
        ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))) := by
    simp only [digitArea, List.cons_append]
    rw [htail, replicate_append_cons]
  have hrun := simDrive_roundFull_stay q b tab s0 m c hm hc x z k K hK hK2
    xc X' hxc hpre m' s' hx h
  refine ((congrArg (fun cfg : Config (stateCountD q b) =>
    (simDrive q b tab s0).run (roundCostStay x z k s') cfg) ?_).trans hrun).trans ?_
  · exact (Config.mk.injEq _ _ _ _).mpr ⟨rfl, by rw [hstart]⟩
  · refine (Config.mk.injEq _ _ _ _).mpr ⟨?_, ?_⟩
    · apply Fin.ext
      simp only [embS, Fin.val_mk, codeState_val]
    · rw [← htail, eraseLen]
      exact tape_eq_enc { state := m', pre := x.pre, cur := s', post := x.post }
        (none :: List.replicate (z + k + 3) (some false) ++ digitArea ks)



/-- **单轮规范形（右移 / right）**：从 `passStart` 出发跑完一轮，回到 `passStart`，
    零计数增加 `k + 3`，计数器变为 `K - 1`，区域更新。
    Canonical right round: `passStart` to `passStart`, zeros grow by `k + 3`,
    the counter becomes `K - 1`. -/
theorem simDrive_roundCanon_right (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (hpre : ∀ c0 ∈ x.pre, c0.2 = false)
    (p : Sym × Bool) (post' : List (Sym × Bool))
    (hp : p.2 = false) (hpost : x.post = p :: post')
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.right))
    (ks : List Nat) (htail : digitArea ks = xc :: X') :
    (simDrive q b tab s0).run (roundCostRight x z k p s')
      (passStart x m c hm hc z (k :: ks)) =
    passStart ({ state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } : Reg q)
      m'.val (K - 1) m'.isLt (by omega) (z + k + 3) ks := by
  have hstart : none :: List.replicate z (some false) ++ digitArea (k :: ks) =
      none :: some false :: (List.replicate z (some false)
        ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))) := by
    simp only [digitArea, List.cons_append]
    rw [htail, replicate_append_cons]
  have hrun := simDrive_roundFull_right q b tab s0 m c hm hc x z k K hK hK2
    xc X' hxc hpre p post' hp hpost m' s' hx h
  refine ((congrArg (fun cfg : Config (stateCountD q b) =>
    (simDrive q b tab s0).run (roundCostRight x z k p s') cfg) ?_).trans hrun).trans ?_
  · exact (Config.mk.injEq _ _ _ _).mpr ⟨rfl, by rw [hstart]⟩
  · refine (Config.mk.injEq _ _ _ _).mpr ⟨?_, ?_⟩
    · apply Fin.ext
      simp only [embS, Fin.val_mk, codeState_val]
    · rw [← htail, eraseLen]
      exact tape_eq_enc { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
        (none :: List.replicate (z + k + 3) (some false) ++ digitArea ks)

/-- **单轮规范形（左移 / left）**：从 `passStart` 出发跑完一轮，回到 `passStart`，
    零计数增加 `k + 3`，计数器变为 `K - 1`，区域更新。
    Canonical left round: `passStart` to `passStart`, zeros grow by `k + 3`,
    the counter becomes `K - 1`. -/
theorem simDrive_roundCanon_left (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) (m c : Nat) (hm : m < q) (hc : c < 2 ^ b)
    (x : Reg q) (z k K : Nat) (hK : K < 2 ^ b) (hK2 : K = k + 2)
    (xc : Sym) (X' : List Sym) (hxc : xc ≠ some true)
    (hpre : ∀ c0 ∈ x.pre, c0.2 = false)
    (cq : Sym × Bool) (pre' : List (Sym × Bool))
    (hq : cq.2 = false) (hpre2 : x.pre = pre' ++ [cq])
    (m' : Fin q) (s' : Sym)
    (hx : x.state = (⟨m, hm⟩ : Fin q))
    (h : pick (tab x.state x.cur) c = some (m', s', Dir.left))
    (ks : List Nat) (htail : digitArea ks = xc :: X') :
    (simDrive q b tab s0).run (roundCostLeft (q := q) z k pre' cq s')
      (passStart x m c hm hc z (k :: ks)) =
    passStart ({ state := m', pre := pre', cur := cq.1, post := (s', false) :: x.post } : Reg q)
      m'.val (K - 1) m'.isLt (by omega) (z + k + 3) ks := by
  have hstart : none :: List.replicate z (some false) ++ digitArea (k :: ks) =
      none :: some false :: (List.replicate z (some false)
        ++ (some true :: (List.replicate (k + 1) (some true) ++ (xc :: X')))) := by
    simp only [digitArea, List.cons_append]
    rw [htail, replicate_append_cons]
  have hrun := simDrive_roundFull_left q b tab s0 m c hm hc x z k K hK hK2
    xc X' hxc hpre cq pre' hq hpre2 m' s' hx h
  refine ((congrArg (fun cfg : Config (stateCountD q b) =>
    (simDrive q b tab s0).run (roundCostLeft (q := q) z k pre' cq s') cfg) ?_).trans hrun).trans ?_
  · exact (Config.mk.injEq _ _ _ _).mpr ⟨rfl, by rw [hstart]⟩
  · refine (Config.mk.injEq _ _ _ _).mpr ⟨?_, ?_⟩
    · apply Fin.ext
      simp only [embS, Fin.val_mk, codeState_val]
    · rw [← htail, eraseLen]
      exact tape_eq_enc (q := q) { state := m', pre := pre', cur := cq.1, post := (s', false) :: x.post }
        (none :: List.replicate (z + k + 3) (some false) ++ digitArea ks)

/-- 通路驱动器（语义递归）：按数字区块逐轮前进，返回累计步数、零计数、计数器与终态区域。
    `none` 表示某一步选择无效或越界（分支死亡）。
    Semantic pass driver over the digit blocks; `none` means the branch died. -/
def passRun (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    (Z c : Nat) → c < 2 ^ b → Reg q → (ks : List Nat) →
    (∀ k' ∈ ks, k' + 2 < 2 ^ b) → Option (PassRes q b)
  | Z, c, hc, x, [], _ => some ⟨0, Z, c, hc, x⟩
  | Z, c, _, x, k :: ks, hb =>
      match pick (tab x.state x.cur) c with
      | some (m', s', Dir.stay) =>
          (passRun q b tab (Z + k + 3) (k + 1)
            (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
            { state := m', pre := x.pre, cur := s', post := x.post } ks
            (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk'))).map
            (fun r => ⟨roundCostStay x Z k s' + r.steps, r.z, r.c, r.hc, r.reg⟩)
      | some (m', s', Dir.right) =>
          match x.post with
          | p :: post' =>
              (passRun q b tab (Z + k + 3) (k + 1)
                (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } ks
                (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk'))).map
                (fun r => ⟨roundCostRight x Z k p s' + r.steps, r.z, r.c, r.hc, r.reg⟩)
          | [] => none
      | some (m', s', Dir.left) =>
          match x.pre.reverse with
          | cq :: preRev =>
              (passRun q b tab (Z + k + 3) (k + 1)
                (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                { state := m', pre := preRev.reverse, cur := cq.1,
                  post := (s', false) :: x.post } ks
                (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk'))).map
                (fun r => ⟨roundCostLeft (q := q) Z k preRev.reverse cq s' + r.steps,
                  r.z, r.c, r.hc, r.reg⟩)
          | [] => none
      | none => none


/-- 数字区总能拆成首符号与余下部分。Digit area can always be split. -/
theorem digitArea_split (ks : List Nat) : ∃ xc X', digitArea ks = xc :: X' := by
  cases ks with
  | nil => exact ⟨none, [], rfl⟩
  | cons k ks => exact ⟨some false, _, rfl⟩



/-- `passRun` 在 stay 分支的展开。`passRun` unfolding for the stay branch. -/
theorem passRun_stay_unfold (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (k : Nat) (ks : List Nat)
    (hb : ∀ k' ∈ k :: ks, k' + 2 < 2 ^ b) (m' : Fin q) (s' : Sym)
    (hpk : pick (tab x.state x.cur) c = some (m', s', Dir.stay)) :
    passRun q b tab Z c hc x (k :: ks) hb =
      (passRun q b tab (Z + k + 3) (k + 1)
        (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
        { state := m', pre := x.pre, cur := s', post := x.post } ks
        (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk'))).map
        (fun r => ⟨roundCostStay x Z k s' + r.steps, r.z, r.c, r.hc, r.reg⟩) := by
  simp only [passRun, hpk]

/-- `passRun` 在 right 分支的展开。`passRun` unfolding for the right branch. -/
theorem passRun_right_unfold (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (k : Nat) (ks : List Nat)
    (hb : ∀ k' ∈ k :: ks, k' + 2 < 2 ^ b) (m' : Fin q) (s' : Sym)
    (p : Sym × Bool) (post' : List (Sym × Bool)) (hpost0 : x.post = p :: post')
    (hpk : pick (tab x.state x.cur) c = some (m', s', Dir.right)) :
    passRun q b tab Z c hc x (k :: ks) hb =
      (passRun q b tab (Z + k + 3) (k + 1)
        (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
        { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } ks
        (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk'))).map
        (fun r => ⟨roundCostRight x Z k p s' + r.steps, r.z, r.c, r.hc, r.reg⟩) := by
  simp only [passRun, hpk, hpost0]

/-- `passRun` 在 left 分支的展开。`passRun` unfolding for the left branch. -/
theorem passRun_left_unfold (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (k : Nat) (ks : List Nat)
    (hb : ∀ k' ∈ k :: ks, k' + 2 < 2 ^ b) (m' : Fin q) (s' : Sym)
    (cq : Sym × Bool) (preRev : List (Sym × Bool)) (hrev : x.pre.reverse = cq :: preRev)
    (hpk : pick (tab x.state x.cur) c = some (m', s', Dir.left)) :
    passRun q b tab Z c hc x (k :: ks) hb =
      (passRun q b tab (Z + k + 3) (k + 1)
        (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
        { state := m', pre := preRev.reverse, cur := cq.1,
          post := (s', false) :: x.post } ks
        (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk'))).map
        (fun r => ⟨roundCostLeft (q := q) Z k preRev.reverse cq s' + r.steps,
          r.z, r.c, r.hc, r.reg⟩) := by
  simp only [passRun, hpk, hrev]

/-- `passRun` 在 pick 失败时的展开。`passRun` unfolding when the pick fails. -/
theorem passRun_none_unfold (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (k : Nat) (ks : List Nat)
    (hb : ∀ k' ∈ k :: ks, k' + 2 < 2 ^ b)
    (hpk : pick (tab x.state x.cur) c = none) :
    passRun q b tab Z c hc x (k :: ks) hb = none := by
  simp only [passRun, hpk]

/-- `passRun` 在右移越界时的展开。`passRun` unfolding on a right out-of-bounds move. -/
theorem passRun_right_nil_unfold (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (k : Nat) (ks : List Nat)
    (hb : ∀ k' ∈ k :: ks, k' + 2 < 2 ^ b) (m' : Fin q) (s' : Sym)
    (hpost0 : x.post = [])
    (hpk : pick (tab x.state x.cur) c = some (m', s', Dir.right)) :
    passRun q b tab Z c hc x (k :: ks) hb = none := by
  simp only [passRun, hpk, hpost0]

/-- `passRun` 在左移越界时的展开。`passRun` unfolding on a left out-of-bounds move. -/
theorem passRun_left_nil_unfold (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (k : Nat) (ks : List Nat)
    (hb : ∀ k' ∈ k :: ks, k' + 2 < 2 ^ b) (m' : Fin q) (s' : Sym)
    (hrev : x.pre.reverse = [])
    (hpk : pick (tab x.state x.cur) c = some (m', s', Dir.left)) :
    passRun q b tab Z c hc x (k :: ks) hb = none := by
  simp only [passRun, hpk, hrev]

/-- **通路主定理**：`passRun` 的每一轮都能由 `simDrive` 实际执行；成功时机器从
    `passStart` 恰好运行 `r.steps` 步到达 `passEnd`。
    Main pass theorem: every `passRun` round is realised by `simDrive`; on success the
    machine runs exactly `r.steps` steps from `passStart` to `passEnd`. -/
theorem simDrive_pass (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir))
    (s0 : Fin q) :
    ∀ (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q) (m : Nat) (hm : m < q),
      x.state = (⟨m, hm⟩ : Fin q) →
      (∀ p0 ∈ x.pre, p0.2 = false) →
      (∀ p0 ∈ x.post, p0.2 = false) →
      (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) →
      ∀ (r : PassRes q b), passRun q b tab Z c hc x L hb = some r →
        (simDrive q b tab s0).run r.steps (passStart x m c hm hc Z L) = passEnd r := by
  intro L
  induction L with
  | nil =>
      intro Z c hc x m hm hx hpre hpost hb r hpass
      simp only [passRun, Option.some.injEq] at hpass
      cases hpass
      simp only [passEnd]
      refine (Config.mk.injEq _ _ _ _).mpr ⟨?_, rfl⟩
      apply Fin.ext
      simp only [embS, Fin.val_mk, codeState_val]
      exact congrArg (fun v => packIdx (2 ^ b) 9 15 v c 0 0) (congrArg Fin.val hx.symm)
  | cons k ks ih =>
      intro Z c hc x m hm hx hpre hpost hb r hpass
      obtain ⟨xc, X', htail⟩ := digitArea_split ks
      have hxc := digitArea_head_ne_true ks xc X' htail
      have hkb : k + 2 < 2 ^ b := hb k (by rw [List.mem_cons]; exact Or.inl rfl)
      have hb' : ∀ k' ∈ ks, k' + 2 < 2 ^ b :=
        fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')
      cases hpk : pick (tab x.state x.cur) c with
      | none =>
          rw [passRun_none_unfold q b tab Z c hc x k ks hb hpk] at hpass
          cases hpass
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [passRun_stay_unfold q b tab Z c hc x k ks hb m' s' hpk] at hpass
              cases hrec : passRun q b tab (Z + k + 3) (k + 1)
                  (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                  { state := m', pre := x.pre, cur := s', post := x.post } ks
                  (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
              | none => rw [hrec] at hpass; cases hpass
              | some r0 =>
                  rw [hrec] at hpass
                  simp only [Option.map_some, Option.some.injEq] at hpass
                  cases hpass
                  have hcan := simDrive_roundCanon_stay q b tab s0 m c hm hc x Z k (k + 2)
                    hkb rfl xc X' hxc hpre m' s' hx hpk ks htail
                  rw [DTM.run_add, hcan]
                  have hx' : ({ state := m', pre := x.pre, cur := s', post := x.post } : Reg q).state
                      = (⟨m'.val, m'.isLt⟩ : Fin q) := by cases m'; rfl
                  have hih := ih (Z + k + 3) (k + 1)
                    (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                    { state := m', pre := x.pre, cur := s', post := x.post } m'.val m'.isLt
                    hx' hpre hpost
                    (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hrec
                  exact hih.trans rfl
          | right =>
              cases hpost0 : x.post with
              | nil =>
                  rw [passRun_right_nil_unfold q b tab Z c hc x k ks hb m' s' hpost0 hpk] at hpass
                  cases hpass
              | cons p post' =>
                  rw [passRun_right_unfold q b tab Z c hc x k ks hb m' s' p post' hpost0 hpk]
                    at hpass
                  cases hrec : passRun q b tab (Z + k + 3) (k + 1)
                      (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                      { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } ks
                      (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
                  | none => rw [hrec] at hpass; cases hpass
                  | some r0 =>
                      rw [hrec] at hpass
                      simp only [Option.map_some, Option.some.injEq] at hpass
                      cases hpass
                      have hp : p.2 = false := hpost p (by rw [hpost0]; simp)
                      have hpre' : ∀ p0 ∈ x.pre ++ [(s', false)], p0.2 = false := by
                        intro p0 hp0
                        rcases List.mem_append.mp hp0 with hp0' | hp0'
                        · exact hpre p0 hp0'
                        · rw [List.mem_singleton] at hp0'
                          subst hp0'
                          rfl
                      have hpost' : ∀ p0 ∈ post', p0.2 = false :=
                        fun p0 hp0 => hpost p0 (by rw [hpost0]; exact List.mem_cons_of_mem _ hp0)
                      have hcan := simDrive_roundCanon_right q b tab s0 m c hm hc x Z k (k + 2)
                        hkb rfl xc X' hxc hpre p post' hp hpost0 m' s' hx hpk ks htail
                      rw [DTM.run_add, hcan]
                      have hx' : (Reg.mk m' (x.pre ++ [(s', false)]) p.1 post' : Reg q).state
                          = (⟨m'.val, m'.isLt⟩ : Fin q) := by cases m'; rfl
                      have hih := ih (Z + k + 3) (k + 1)
                        (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                        { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                        m'.val m'.isLt hx' hpre' hpost'
                        (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hrec
                      exact hih.trans rfl
          | left =>
              cases hrev : x.pre.reverse with
              | nil =>
                  rw [passRun_left_nil_unfold q b tab Z c hc x k ks hb m' s' hrev hpk] at hpass
                  cases hpass
              | cons cq preRev =>
                  rw [passRun_left_unfold q b tab Z c hc x k ks hb m' s' cq preRev hrev hpk]
                    at hpass
                  cases hrec : passRun q b tab (Z + k + 3) (k + 1)
                      (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                      (Reg.mk m' preRev.reverse cq.1 ((s', false) :: x.post)) ks
                      (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
                  | none => rw [hrec] at hpass; cases hpass
                  | some r0 =>
                      rw [hrec] at hpass
                      simp only [Option.map_some, Option.some.injEq] at hpass
                      cases hpass
                      have hpre2 : x.pre = preRev.reverse ++ [cq] := by
                        rw [← List.reverse_reverse x.pre, hrev, List.reverse_cons]
                      have hq : cq.2 = false :=
                        hpre cq (by rw [hpre2]; exact List.mem_append_right _ (by simp))
                      have hpre' : ∀ p0 ∈ preRev.reverse, p0.2 = false := by
                        intro p0 hp0
                        exact hpre p0 (by rw [hpre2]; exact List.mem_append_left _ hp0)
                      have hpost' : ∀ p0 ∈ (s', false) :: x.post, p0.2 = false := by
                        intro p0 hp0
                        rcases List.mem_cons.mp hp0 with rfl | hp0'
                        · rfl
                        · exact hpost p0 hp0'
                      have hcan := simDrive_roundCanon_left q b tab s0 m c hm hc x Z k (k + 2)
                        hkb rfl xc X' hxc hpre cq preRev.reverse hq hpre2 m' s' hx hpk ks htail
                      rw [DTM.run_add, hcan]
                      have hx' : (Reg.mk m' preRev.reverse cq.1 ((s', false) :: x.post) : Reg q).state
                          = (⟨m'.val, m'.isLt⟩ : Fin q) := by cases m'; rfl
                      have hih := ih (Z + k + 3) (k + 1)
                        (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                        { state := m', pre := preRev.reverse, cur := cq.1,
                          post := (s', false) :: x.post } m'.val m'.isLt hx' hpre' hpost'
                        (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hrec
                      exact hih.trans rfl

/-- 通路的选择序列：第 1 轮用 `c`，之后每轮用前一块的 `k + 1`（长度 = 块数）。
    Choice sequence of a pass: `c` first, then each block's `k + 1`. -/
def passChoices (c : Nat) : List Nat → List Nat
  | [] => []
  | k :: ks => c :: passChoices (k + 1) ks

/-- 按选择列表逐步迭代区域单步（语义侧，对应 `NTM.runWith` 的选择消费）。
    Iterate the region step over a choice list. -/
def stepCs {q : Nat} (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    List Nat → Reg q → Option (Reg q)
  | [], x => some x
  | c :: cs, x => (Reg.step tab c x).bind (stepCs tab cs)

/-- **通路 = 区域迭代**：`passRun` 成功时，其终态区域正是按选择序列逐步
    `Reg.step` 的结果。Pass success implies the register equals iterated `Reg.step`. -/
theorem passRun_reg (q b : Nat) (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    ∀ (L : List Nat) (c Z : Nat) (hc : c < 2 ^ b) (x : Reg q)
      (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) (r : PassRes q b),
      passRun q b tab Z c hc x L hb = some r →
      stepCs tab (passChoices c L) x = some r.reg := by
  intro L
  induction L with
  | nil =>
      intro c Z hc x hb r hpass
      simp only [passRun, Option.some.injEq] at hpass
      cases hpass
      simp only [passChoices, stepCs]
  | cons k ks ih =>
      intro c Z hc x hb r hpass
      cases hpk : pick (tab x.state x.cur) c with
      | none =>
          rw [passRun_none_unfold q b tab Z c hc x k ks hb hpk] at hpass
          cases hpass
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [passRun_stay_unfold q b tab Z c hc x k ks hb m' s' hpk] at hpass
              cases hrec : passRun q b tab (Z + k + 3) (k + 1)
                  (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                  { state := m', pre := x.pre, cur := s', post := x.post } ks
                  (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
              | none => rw [hrec] at hpass; cases hpass
              | some r0 =>
                  rw [hrec] at hpass
                  simp only [Option.map_some, Option.some.injEq] at hpass
                  cases hpass
                  simp only [passChoices, stepCs]
                  rw [show Reg.step tab c x
                      = some { state := m', pre := x.pre, cur := s', post := x.post } from by
                    simp only [Reg.step, hpk]]
                  simp only [Option.bind_some]
                  exact ih (k + 1) (Z + k + 3)
                    (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                    { state := m', pre := x.pre, cur := s', post := x.post }
                    (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hrec
          | right =>
              cases hpost0 : x.post with
              | nil =>
                  rw [passRun_right_nil_unfold q b tab Z c hc x k ks hb m' s' hpost0 hpk] at hpass
                  cases hpass
              | cons p post' =>
                  rw [passRun_right_unfold q b tab Z c hc x k ks hb m' s' p post' hpost0 hpk]
                    at hpass
                  cases hrec : passRun q b tab (Z + k + 3) (k + 1)
                      (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                      { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' } ks
                      (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
                  | none => rw [hrec] at hpass; cases hpass
                  | some r0 =>
                      rw [hrec] at hpass
                      simp only [Option.map_some, Option.some.injEq] at hpass
                      cases hpass
                      simp only [passChoices, stepCs]
                      rw [show Reg.step tab c x
                          = some (Reg.mk m' (x.pre ++ [(s', false)]) p.1 post') from by
                        simp only [Reg.step, hpk, hpost0]]
                      simp only [Option.bind_some]
                      exact ih (k + 1) (Z + k + 3)
                        (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                        { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                        (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hrec
          | left =>
              cases hrev : x.pre.reverse with
              | nil =>
                  rw [passRun_left_nil_unfold q b tab Z c hc x k ks hb m' s' hrev hpk] at hpass
                  cases hpass
              | cons cq preRev =>
                  rw [passRun_left_unfold q b tab Z c hc x k ks hb m' s' cq preRev hrev hpk]
                    at hpass
                  cases hrec : passRun q b tab (Z + k + 3) (k + 1)
                      (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                      (Reg.mk m' preRev.reverse cq.1 ((s', false) :: x.post)) ks
                      (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) with
                  | none => rw [hrec] at hpass; cases hpass
                  | some r0 =>
                      rw [hrec] at hpass
                      simp only [Option.map_some, Option.some.injEq] at hpass
                      cases hpass
                      simp only [passChoices, stepCs]
                      rw [show Reg.step tab c x
                          = some (Reg.mk m' preRev.reverse cq.1 ((s', false) :: x.post)) from by
                        simp only [Reg.step, hpk, hrev]]
                      simp only [Option.bind_some]
                      exact ih (k + 1) (Z + k + 3)
                        (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
                        (Reg.mk m' preRev.reverse cq.1 ((s', false) :: x.post))
                        (fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')) r0 hrec

/-! ## 区域两侧格数的守恒（供给越界记账） -/

/-- `passRun` 成功时右侧格数的下界：每轮最多消耗一格右侧，故初值 ≤ 终值 + 轮数。
    Right-side cell count bound: each round consumes at most one post cell. -/
theorem passRun_post_ge (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    ∀ (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q)
      (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) (r : PassRes q b),
      passRun q b tab Z c hc x L hb = some r →
      x.post.length ≤ r.reg.post.length + L.length := by
  intro L
  induction L with
  | nil =>
      intro Z c hc x hb r hpass
      simp only [passRun, Option.some.injEq] at hpass
      subst hpass
      simp only [List.length_nil, Nat.add_zero]
      omega
  | cons k ks ih =>
      intro Z c hc x hb r hpass
      have hcK : k + 1 < 2 ^ b :=
        (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
      have hb' : ∀ k' ∈ ks, k' + 2 < 2 ^ b :=
        fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')
      cases hpk : pick (tab x.state x.cur) c with
      | none =>
          rw [passRun_none_unfold q b tab Z c hc x k ks hb hpk] at hpass
          cases hpass
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [passRun_stay_unfold q b tab Z c hc x k ks hb m' s' hpk] at hpass
              cases hrec : passRun q b tab (Z + k + 3) (k + 1) hcK
                  { state := m', pre := x.pre, cur := s', post := x.post } ks hb' with
              | none => rw [hrec] at hpass; cases hpass
              | some r0 =>
                  rw [hrec] at hpass
                  simp only [Option.map_some, Option.some.injEq] at hpass
                  subst hpass
                  have h := ih (Z + k + 3) (k + 1) hcK
                    { state := m', pre := x.pre, cur := s', post := x.post } hb' r0 hrec
                  dsimp only at h ⊢
                  simp only [List.length_cons] at h ⊢
                  omega
          | right =>
              cases hpost0 : x.post with
              | nil =>
                  rw [passRun_right_nil_unfold q b tab Z c hc x k ks hb m' s' hpost0 hpk]
                    at hpass
                  cases hpass
              | cons p post' =>
                  rw [passRun_right_unfold q b tab Z c hc x k ks hb m' s' p post' hpost0 hpk]
                    at hpass
                  cases hrec : passRun q b tab (Z + k + 3) (k + 1) hcK
                      { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                      ks hb' with
                  | none => rw [hrec] at hpass; cases hpass
                  | some r0 =>
                      rw [hrec] at hpass
                      simp only [Option.map_some, Option.some.injEq] at hpass
                      subst hpass
                      have h := ih (Z + k + 3) (k + 1) hcK
                        { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                        hb' r0 hrec
                      dsimp only at h ⊢
                      simp only [List.length_cons] at h ⊢
                      omega
          | left =>
              cases hrev : x.pre.reverse with
              | nil =>
                  rw [passRun_left_nil_unfold q b tab Z c hc x k ks hb m' s' hrev hpk] at hpass
                  cases hpass
              | cons cq preRev =>
                  rw [passRun_left_unfold q b tab Z c hc x k ks hb m' s' cq preRev hrev hpk]
                    at hpass
                  cases hrec : passRun q b tab (Z + k + 3) (k + 1) hcK
                      { state := m', pre := preRev.reverse, cur := cq.1,
                        post := (s', false) :: x.post } ks hb' with
                  | none => rw [hrec] at hpass; cases hpass
                  | some r0 =>
                      rw [hrec] at hpass
                      simp only [Option.map_some, Option.some.injEq] at hpass
                      subst hpass
                      have h := ih (Z + k + 3) (k + 1) hcK
                        { state := m', pre := preRev.reverse, cur := cq.1,
                          post := (s', false) :: x.post } hb' r0 hrec
                      dsimp only at h ⊢
                      simp only [List.length_cons] at h ⊢
                      omega

/-- `passRun` 成功时左侧格数的下界（对偶结论）。
    Left-side cell count bound: each round consumes at most one pre cell. -/
theorem passRun_pre_ge (q b : Nat)
    (tab : Fin q → Sym → List (Fin q × Sym × Dir)) :
    ∀ (L : List Nat) (Z c : Nat) (hc : c < 2 ^ b) (x : Reg q)
      (hb : ∀ k' ∈ L, k' + 2 < 2 ^ b) (r : PassRes q b),
      passRun q b tab Z c hc x L hb = some r →
      x.pre.length ≤ r.reg.pre.length + L.length := by
  intro L
  induction L with
  | nil =>
      intro Z c hc x hb r hpass
      simp only [passRun, Option.some.injEq] at hpass
      subst hpass
      simp only [List.length_nil, Nat.add_zero]
      omega
  | cons k ks ih =>
      intro Z c hc x hb r hpass
      have hcK : k + 1 < 2 ^ b :=
        (by have := hb k (by rw [List.mem_cons]; exact Or.inl rfl); omega)
      have hb' : ∀ k' ∈ ks, k' + 2 < 2 ^ b :=
        fun k' hk' => hb k' (by rw [List.mem_cons]; exact Or.inr hk')
      cases hpk : pick (tab x.state x.cur) c with
      | none =>
          rw [passRun_none_unfold q b tab Z c hc x k ks hb hpk] at hpass
          cases hpass
      | some v =>
          obtain ⟨m', s', d⟩ := v
          cases d with
          | stay =>
              rw [passRun_stay_unfold q b tab Z c hc x k ks hb m' s' hpk] at hpass
              cases hrec : passRun q b tab (Z + k + 3) (k + 1) hcK
                  { state := m', pre := x.pre, cur := s', post := x.post } ks hb' with
              | none => rw [hrec] at hpass; cases hpass
              | some r0 =>
                  rw [hrec] at hpass
                  simp only [Option.map_some, Option.some.injEq] at hpass
                  subst hpass
                  have h := ih (Z + k + 3) (k + 1) hcK
                    { state := m', pre := x.pre, cur := s', post := x.post } hb' r0 hrec
                  dsimp only at h ⊢
                  simp only [List.length_cons] at h ⊢
                  omega
          | right =>
              cases hpost0 : x.post with
              | nil =>
                  rw [passRun_right_nil_unfold q b tab Z c hc x k ks hb m' s' hpost0 hpk]
                    at hpass
                  cases hpass
              | cons p post' =>
                  rw [passRun_right_unfold q b tab Z c hc x k ks hb m' s' p post' hpost0 hpk]
                    at hpass
                  cases hrec : passRun q b tab (Z + k + 3) (k + 1) hcK
                      { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                      ks hb' with
                  | none => rw [hrec] at hpass; cases hpass
                  | some r0 =>
                      rw [hrec] at hpass
                      simp only [Option.map_some, Option.some.injEq] at hpass
                      subst hpass
                      have h := ih (Z + k + 3) (k + 1) hcK
                        { state := m', pre := x.pre ++ [(s', false)], cur := p.1, post := post' }
                        hb' r0 hrec
                      dsimp only at h ⊢
                      simp only [List.length_append, List.length_cons] at h ⊢
                      omega
          | left =>
              cases hrev : x.pre.reverse with
              | nil =>
                  rw [passRun_left_nil_unfold q b tab Z c hc x k ks hb m' s' hrev hpk] at hpass
                  cases hpass
              | cons cq preRev =>
                  rw [passRun_left_unfold q b tab Z c hc x k ks hb m' s' cq preRev hrev hpk]
                    at hpass
                  cases hrec : passRun q b tab (Z + k + 3) (k + 1) hcK
                      { state := m', pre := preRev.reverse, cur := cq.1,
                        post := (s', false) :: x.post } ks hb' with
                  | none => rw [hrec] at hpass; cases hpass
                  | some r0 =>
                      rw [hrec] at hpass
                      simp only [Option.map_some, Option.some.injEq] at hpass
                      subst hpass
                      have h := ih (Z + k + 3) (k + 1) hcK
                        { state := m', pre := preRev.reverse, cur := cq.1,
                          post := (s', false) :: x.post } hb' r0 hrec
                      have hlen : x.pre.length = preRev.length + 1 := by
                        have := congrArg List.length hrev
                        simp only [List.length_reverse, List.length_cons] at this
                        omega
                      dsimp only at h ⊢
                      simp only [List.length_reverse, List.length_cons] at h ⊢
                      omega

end DTM

end Pnp
