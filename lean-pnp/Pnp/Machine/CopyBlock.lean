/-
  文件：Pnp/Machine/CopyBlock.lean
  File: Pnp/Machine/CopyBlock.lean

  主题：**格块左向转写机 `copyCells`**——逐个读取源格的标记位 `some true` 格，
        把其镜像格 `[codeFst, codeSnd, some false]` 写到左侧已写块末端，源格标记翻成 `false`
        作为「已读」标记；头回到下一个未读格（标记 `some true`）或块后空白。
  Topic: transcribe a `true`-marked cell block leftwards, consuming each source cell,
  and land on the next unread (`true`-marked) cell or on the blank after the block.

  几何（#179 定案）：入口头放在**最左源格的标记位**，自左向右消费；每轮把镜像格写进
  区域左侧预留的 3 个空白格，输出块是源块的**逆序镜像**（标记位全为 `false`），随后停机接受。
  Geometry (#179): the head starts at the leftmost marker and consumes cells left to right;
  each round writes the mirror cell into 3 reserved blanks left of the region, so the output
  is the reversed mirror block (all markers `false`), then the machine halts and accepts.
  验证状态：读格 / 走左 / 写格 / 回扫 / 回右五段与「首轮 / 后续轮」均已形式化（见下）。
  Status: all five segments plus the first-round / later-round lemmas are formalized.
  状态段：10 入口（读标记）；11/12 读 `codeSnd`；20..23 读 `codeFst` 并左走至空白；
  30..33 写标记位；34..37 写 `codeSnd`；38..41 写 `codeFst`；42..49 右行两格；
  50..57 扫描三元组找下一个 `some true`；58..61 标记位判定；99 接受。
-/

import Pnp.Machine.CopyCell

namespace Pnp

namespace DTM

/-- **格块左向转写机**（128 状态，实际用 10–61 与 99）。 -/
def copyCells : DTM 128 where
  step := fun st a =>
    match st.val with
    | 10 =>
      (match a with
       | some true => (⟨4, by omega⟩, some false, Dir.left)
       | _ => (⟨99, by omega⟩, a, Dir.stay))
    | 4 =>
      (match a with
       | some b2 => (⟨6 + (match b2 with | true => 1 | false => 0), by split <;> omega⟩, some b2, Dir.left)
       | none => (⟨99, by omega⟩, a, Dir.stay))
    | 6 =>
      (match a with
       | some b1 => (⟨20 + (match b1 with | true => 2 | false => 0) + 0, by split <;> omega⟩, some b1, Dir.left)
       | none => (⟨99, by omega⟩, a, Dir.stay))
    | 7 =>
      (match a with
       | some b1 => (⟨20 + (match b1 with | true => 2 | false => 0) + 1, by split <;> omega⟩, some b1, Dir.left)
       | none => (⟨99, by omega⟩, a, Dir.stay))
    | 20 =>
      (match a with
       | none => (⟨30, by omega⟩, none, Dir.stay)
       | some b => (⟨20, by omega⟩, some b, Dir.left))
    | 21 =>
      (match a with
       | none => (⟨31, by omega⟩, none, Dir.stay)
       | some b => (⟨21, by omega⟩, some b, Dir.left))
    | 22 =>
      (match a with
       | none => (⟨32, by omega⟩, none, Dir.stay)
       | some b => (⟨22, by omega⟩, some b, Dir.left))
    | 23 =>
      (match a with
       | none => (⟨33, by omega⟩, none, Dir.stay)
       | some b => (⟨23, by omega⟩, some b, Dir.left))
    | 30 => (⟨34, by omega⟩, some false, Dir.left)
    | 31 => (⟨35, by omega⟩, some false, Dir.left)
    | 32 => (⟨36, by omega⟩, some false, Dir.left)
    | 33 => (⟨37, by omega⟩, some false, Dir.left)
    | 34 => (⟨38, by omega⟩, some false, Dir.left)
    | 35 => (⟨39, by omega⟩, some true, Dir.left)
    | 36 => (⟨40, by omega⟩, some false, Dir.left)
    | 37 => (⟨41, by omega⟩, some true, Dir.left)
    | 38 => (⟨42, by omega⟩, some false, Dir.right)
    | 39 => (⟨43, by omega⟩, some false, Dir.right)
    | 40 => (⟨44, by omega⟩, some true, Dir.right)
    | 41 => (⟨45, by omega⟩, some true, Dir.right)
    | 42 => (⟨46, by omega⟩, a, Dir.right)
    | 43 => (⟨47, by omega⟩, a, Dir.right)
    | 44 => (⟨48, by omega⟩, a, Dir.right)
    | 45 => (⟨49, by omega⟩, a, Dir.right)
    | 46 => (⟨50, by omega⟩, a, Dir.right)
    | 47 => (⟨51, by omega⟩, a, Dir.right)
    | 48 => (⟨52, by omega⟩, a, Dir.right)
    | 49 => (⟨53, by omega⟩, a, Dir.right)
    | 50 =>
      (match a with
       | none => (⟨99, by omega⟩, none, Dir.stay)
       | some _ => (⟨54, by omega⟩, a, Dir.right))
    | 51 =>
      (match a with
       | none => (⟨99, by omega⟩, none, Dir.stay)
       | some _ => (⟨55, by omega⟩, a, Dir.right))
    | 52 =>
      (match a with
       | none => (⟨99, by omega⟩, none, Dir.stay)
       | some _ => (⟨56, by omega⟩, a, Dir.right))
    | 53 =>
      (match a with
       | none => (⟨99, by omega⟩, none, Dir.stay)
       | some _ => (⟨57, by omega⟩, a, Dir.right))
    | 54 =>
      (match a with
       | none => (⟨99, by omega⟩, none, Dir.stay)
       | some _ => (⟨58, by omega⟩, a, Dir.right))
    | 55 =>
      (match a with
       | none => (⟨99, by omega⟩, none, Dir.stay)
       | some _ => (⟨59, by omega⟩, a, Dir.right))
    | 56 =>
      (match a with
       | none => (⟨99, by omega⟩, none, Dir.stay)
       | some _ => (⟨60, by omega⟩, a, Dir.right))
    | 57 =>
      (match a with
       | none => (⟨99, by omega⟩, none, Dir.stay)
       | some _ => (⟨61, by omega⟩, a, Dir.right))
    | 58 =>
      (match a with
       | some true => (⟨10, by omega⟩, a, Dir.stay)
       | none => (⟨99, by omega⟩, none, Dir.stay)
       | some false => (⟨50, by omega⟩, a, Dir.right))
    | 59 =>
      (match a with
       | some true => (⟨10, by omega⟩, a, Dir.stay)
       | none => (⟨99, by omega⟩, none, Dir.stay)
       | some false => (⟨51, by omega⟩, a, Dir.right))
    | 60 =>
      (match a with
       | some true => (⟨10, by omega⟩, a, Dir.stay)
       | none => (⟨99, by omega⟩, none, Dir.stay)
       | some false => (⟨52, by omega⟩, a, Dir.right))
    | 61 =>
      (match a with
       | some true => (⟨10, by omega⟩, a, Dir.stay)
       | none => (⟨99, by omega⟩, none, Dir.stay)
       | some false => (⟨53, by omega⟩, a, Dir.right))
    | _ => (st, a, Dir.stay)
  start := ⟨10, by omega⟩
  accept := ⟨99, by omega⟩
  reject := ⟨99, by omega⟩


/-- `some true` 记 1、其余记 0（状态位编码）。 Marker bit as a Nat flag. -/
def bitOf : Sym → Nat
  | some true => 1
  | _ => 0

/-- 标记位取值不超过 1。 The marker flag is at most one. -/
theorem bitOf_le_one (a : Sym) : bitOf a ≤ 1 := by
  cases a with
  | none => simp [bitOf]
  | some b => cases b <;> simp [bitOf]

/-- 非 99 状态一律不停机。 Non-99 states never halt. -/
theorem copyCells_halted_ne (st : Nat) (hst : st < 128) (h : st ≠ 99) (t : Tape) :
    copyCells.halted ⟨⟨st, hst⟩, t⟩ = false := by
  simp only [DTM.halted, copyCells]
  rw [Bool.or_self, beq_eq_false_iff_ne]
  intro hh
  exact h (congrArg Fin.val hh)

/-- `copyCells` 的单步运行套路。 The one-step idiom for `copyCells`. -/
theorem estepC (st : Nat) (hst : st < 128) (a : Sym) (q' : Fin 128) (s : Sym) (d : Dir)
    (h : copyCells.step ⟨st, hst⟩ a = (q', s, d)) (M R : List Sym) (hne : st ≠ 99) :
    copyCells.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (copyCells_halted_ne st hst hne _)]
  exact stepConfig_of_step copyCells ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- 读格段（字面量实例：`codeFst = some false`、`codeSnd = some false`）。 -/
theorem copyCells_read3_ff (x : Sym) (L R : List Sym) :
    copyCells.run 3
      ⟨(⟨10, by omega⟩ : Fin 128),
        Tape.mk (some false :: some false :: x :: L) (some true :: R)⟩
      = ⟨(⟨20, by omega⟩ : Fin 128),
          Tape.mk L (x :: some false :: some false :: some false :: R)⟩ := by
  rw [show (3 : Nat) = 1 + (1 + 1) from rfl]
  rw [DTM.run_add copyCells 1 (1 + 1)]
  rw [estepC 10 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [DTM.run_add copyCells 1 1]
  rw [estepC 4 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [estepC 6 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- 读格段（字面量实例：`codeFst = some false`、`codeSnd = some true`）。 -/
theorem copyCells_read3_ft (x : Sym) (L R : List Sym) :
    copyCells.run 3
      ⟨(⟨10, by omega⟩ : Fin 128),
        Tape.mk (some true :: some false :: x :: L) (some true :: R)⟩
      = ⟨(⟨21, by omega⟩ : Fin 128),
          Tape.mk L (x :: some false :: some true :: some false :: R)⟩ := by
  rw [show (3 : Nat) = 1 + (1 + 1) from rfl]
  rw [DTM.run_add copyCells 1 (1 + 1)]
  rw [estepC 10 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [DTM.run_add copyCells 1 1]
  rw [estepC 4 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [estepC 7 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- 读格段（字面量实例：`codeFst = some true`、`codeSnd = some true`）。 -/
theorem copyCells_read3_tt (x : Sym) (L R : List Sym) :
    copyCells.run 3
      ⟨(⟨10, by omega⟩ : Fin 128),
        Tape.mk (some true :: some true :: x :: L) (some true :: R)⟩
      = ⟨(⟨23, by omega⟩ : Fin 128),
          Tape.mk L (x :: some true :: some true :: some false :: R)⟩ := by
  rw [show (3 : Nat) = 1 + (1 + 1) from rfl]
  rw [DTM.run_add copyCells 1 (1 + 1)]
  rw [estepC 10 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [DTM.run_add copyCells 1 1]
  rw [estepC 4 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [estepC 7 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- **读格段（3 步）**：头在源格标记位时，3 步翻标记并读到两个编码符号，
    头落到格左邻 `x`；状态位 `20 + 2·b1 + b2`。
    The 3-step read phase of `copyCells`. -/
theorem copyCells_read3 (a : Sym) (x : Sym) (L R : List Sym) :
    copyCells.run 3
      ⟨(⟨10, by omega⟩ : Fin 128),
        Tape.mk (codeSnd a :: codeFst a :: x :: L) (some true :: R)⟩
      = ⟨(⟨20 + 2 * bitOf (codeFst a) + bitOf (codeSnd a), by
              have h1 := bitOf_le_one (codeFst a)
              have h2 := bitOf_le_one (codeSnd a)
              omega⟩ : Fin 128),
          Tape.mk L (x :: codeFst a :: codeSnd a :: some false :: R)⟩ := by
  cases a with
  | none => simpa only [codeFst, codeSnd, symCode, bitOf, List.headD_cons, List.drop_zero,
        List.drop_succ_cons] using copyCells_read3_ff x L R
  | some b => cases b with
    | false => simpa only [codeFst, codeSnd, symCode, bitOf, List.headD_cons, List.drop_zero,
        List.drop_succ_cons] using copyCells_read3_ft x L R
    | true => simpa only [codeFst, codeSnd, symCode, bitOf, List.headD_cons, List.drop_zero,
        List.drop_succ_cons] using copyCells_read3_tt x L R


/-! ### 走左段（状态 20..23 → 30..33） -/

/-- 小于 4 的自然数只有 0/1/2/3（零依赖枚举）。 `n < 4` enumerates four cases. -/
theorem nat_lt4_cases {n : Nat} (h : n < 4) : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 := by omega

/-- **走左段（通用循环）**：状态 `q` 读到非空白即原地左移，读到空白转 `q'` 并停留。
    在「非空白串 `l` + 空白」前缀上，`l.length + 2` 步后头停在空白上、状态为 `q'`。
    Generic left-walk loop: step left on every non-blank, stop on blank. -/
theorem copyCells_walkLoop (q : Nat) (hq : q < 128) (hne : q ≠ 99) (q' : Fin 128)
    (hstep : ∀ b : Bool, copyCells.step ⟨q, hq⟩ (some b) = (⟨q, hq⟩, some b, Dir.left))
    (hstop : copyCells.step ⟨q, hq⟩ none = (q', none, Dir.stay)) :
    ∀ (l : List Sym), (∀ y ∈ l, y ≠ none) → ∀ (b : Bool) (L0 R : List Sym),
      copyCells.run (l.length + 2) ⟨⟨q, hq⟩, Tape.mk (l ++ none :: L0) (some b :: R)⟩
        = ⟨q', Tape.mk L0 (none :: l.reverse ++ some b :: R)⟩
  | [], _, b, L0, R => by
      -- 两步：读到 `some b` 左移一格，再读到空白转 `q'` 停留
      rw [show ([] : List Sym).length + 2 = 1 + 1 from by simp]
      rw [DTM.run_add copyCells 1 1]
      rw [estepC q hq (some b) ⟨q, hq⟩ (some b) Dir.left (hstep b) ([] ++ none :: L0) R hne]
      etape
      rw [estepC q hq none q' none Dir.stay hstop L0 (some b :: R) hne]
      etape
      simp only [List.reverse_nil, List.nil_append]
  | a :: t, hl, b, L0, R => by
      -- 首符号非空白，故形如 `some a'`：先左移一格，再交给归纳假设
      have ha : a ≠ none := hl a (by simp)
      cases a with
      | none => exact absurd rfl ha
      | some a' =>
        rw [show ((some a' :: t).length + 2 : Nat) = 1 + (t.length + 2) from by
              simp only [List.length_cons]; omega]
        rw [DTM.run_add copyCells 1 (t.length + 2)]
        rw [estepC q hq (some b) ⟨q, hq⟩ (some b) Dir.left (hstep b)
          ((some a' :: t) ++ none :: L0) R hne]
        etape
        rw [copyCells_walkLoop q hq hne q' hstep hstop t
          (by intro y hy; exact hl y (List.mem_cons_of_mem _ hy)) a' L0 (some b :: R)]
        simp only [List.reverse_cons, List.cons_append, List.append_assoc, List.nil_append]

/-- 走左段（状态 20）。 Left-walk at state 20. -/
theorem copyCells_walkL20 :
    ∀ (l : List Sym), (∀ y ∈ l, y ≠ none) → ∀ (b : Bool) (L0 R : List Sym),
      copyCells.run (l.length + 2)
        ⟨(⟨20, by omega⟩ : Fin 128), Tape.mk (l ++ none :: L0) (some b :: R)⟩
        = ⟨(⟨30, by omega⟩ : Fin 128), Tape.mk L0 (none :: l.reverse ++ some b :: R)⟩ :=
  copyCells_walkLoop 20 (by omega) (by omega) ⟨30, by omega⟩
    (by intro b; cases b <;> rfl) (by rfl)

/-- 走左段（状态 21）。 Left-walk at state 21. -/
theorem copyCells_walkL21 :
    ∀ (l : List Sym), (∀ y ∈ l, y ≠ none) → ∀ (b : Bool) (L0 R : List Sym),
      copyCells.run (l.length + 2)
        ⟨(⟨21, by omega⟩ : Fin 128), Tape.mk (l ++ none :: L0) (some b :: R)⟩
        = ⟨(⟨31, by omega⟩ : Fin 128), Tape.mk L0 (none :: l.reverse ++ some b :: R)⟩ :=
  copyCells_walkLoop 21 (by omega) (by omega) ⟨31, by omega⟩
    (by intro b; cases b <;> rfl) (by rfl)

/-- 走左段（状态 22）。 Left-walk at state 22. -/
theorem copyCells_walkL22 :
    ∀ (l : List Sym), (∀ y ∈ l, y ≠ none) → ∀ (b : Bool) (L0 R : List Sym),
      copyCells.run (l.length + 2)
        ⟨(⟨22, by omega⟩ : Fin 128), Tape.mk (l ++ none :: L0) (some b :: R)⟩
        = ⟨(⟨32, by omega⟩ : Fin 128), Tape.mk L0 (none :: l.reverse ++ some b :: R)⟩ :=
  copyCells_walkLoop 22 (by omega) (by omega) ⟨32, by omega⟩
    (by intro b; cases b <;> rfl) (by rfl)

/-- 走左段（状态 23）。 Left-walk at state 23. -/
theorem copyCells_walkL23 :
    ∀ (l : List Sym), (∀ y ∈ l, y ≠ none) → ∀ (b : Bool) (L0 R : List Sym),
      copyCells.run (l.length + 2)
        ⟨(⟨23, by omega⟩ : Fin 128), Tape.mk (l ++ none :: L0) (some b :: R)⟩
        = ⟨(⟨33, by omega⟩ : Fin 128), Tape.mk L0 (none :: l.reverse ++ some b :: R)⟩ :=
  copyCells_walkLoop 23 (by omega) (by omega) ⟨33, by omega⟩
    (by intro b; cases b <;> rfl) (by rfl)

/-- **走左段**：状态 `20 + i`（`i < 4`）左行越过非空白串 `l`，停在空白上转入 `30 + i`。
    The left-walk segment for any `i < 4`. -/
theorem copyCells_walkL (i : Nat) (hi : i < 4) :
    ∀ (l : List Sym), (∀ y ∈ l, y ≠ none) → ∀ (b : Bool) (L0 R : List Sym),
      copyCells.run (l.length + 2)
        ⟨(⟨20 + i, by omega⟩ : Fin 128), Tape.mk (l ++ none :: L0) (some b :: R)⟩
        = ⟨(⟨30 + i, by omega⟩ : Fin 128), Tape.mk L0 (none :: l.reverse ++ some b :: R)⟩ := by
  rcases nat_lt4_cases hi with h | h | h | h
  · subst h; exact copyCells_walkL20
  · subst h; exact copyCells_walkL21
  · subst h; exact copyCells_walkL22
  · subst h; exact copyCells_walkL23


/-! ### 写格段（状态 30..41 → 42..45） -/

/-- 写格段（状态 30，位值 `(b1,b2) = (0,0)`）：写标记 + 两编码位，头回到格右邻。 -/
theorem copyCells_write3_0 (L2 R : List Sym) :
    copyCells.run 3
      ⟨(⟨30, by omega⟩ : Fin 128), Tape.mk (none :: none :: L2) (none :: R)⟩
      = ⟨(⟨42, by omega⟩ : Fin 128),
          Tape.mk (some false :: L2) (some false :: some false :: R)⟩ := by
  rw [show (3 : Nat) = 1 + (1 + 1) from rfl]
  rw [DTM.run_add copyCells 1 (1 + 1)]
  rw [estepC 30 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [DTM.run_add copyCells 1 1]
  rw [estepC 34 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [estepC 38 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- 写格段（状态 31，位值 `(0,1)`）。 -/
theorem copyCells_write3_1 (L2 R : List Sym) :
    copyCells.run 3
      ⟨(⟨31, by omega⟩ : Fin 128), Tape.mk (none :: none :: L2) (none :: R)⟩
      = ⟨(⟨43, by omega⟩ : Fin 128),
          Tape.mk (some false :: L2) (some true :: some false :: R)⟩ := by
  rw [show (3 : Nat) = 1 + (1 + 1) from rfl]
  rw [DTM.run_add copyCells 1 (1 + 1)]
  rw [estepC 31 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [DTM.run_add copyCells 1 1]
  rw [estepC 35 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [estepC 39 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- 写格段（状态 32，位值 `(1,0)`）。 -/
theorem copyCells_write3_2 (L2 R : List Sym) :
    copyCells.run 3
      ⟨(⟨32, by omega⟩ : Fin 128), Tape.mk (none :: none :: L2) (none :: R)⟩
      = ⟨(⟨44, by omega⟩ : Fin 128),
          Tape.mk (some true :: L2) (some false :: some false :: R)⟩ := by
  rw [show (3 : Nat) = 1 + (1 + 1) from rfl]
  rw [DTM.run_add copyCells 1 (1 + 1)]
  rw [estepC 32 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [DTM.run_add copyCells 1 1]
  rw [estepC 36 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [estepC 40 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- 写格段（状态 33，位值 `(1,1)`）。 -/
theorem copyCells_write3_3 (L2 R : List Sym) :
    copyCells.run 3
      ⟨(⟨33, by omega⟩ : Fin 128), Tape.mk (none :: none :: L2) (none :: R)⟩
      = ⟨(⟨45, by omega⟩ : Fin 128),
          Tape.mk (some true :: L2) (some true :: some false :: R)⟩ := by
  rw [show (3 : Nat) = 1 + (1 + 1) from rfl]
  rw [DTM.run_add copyCells 1 (1 + 1)]
  rw [estepC 33 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [DTM.run_add copyCells 1 1]
  rw [estepC 37 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [estepC 41 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- **写格段（3 步）**：状态 `30 + i` 在空白格左向写下 `[codeFst, codeSnd, marker=false]`
    三个符号，头落回标记位右侧、状态 `42 + i`。
    The 3-step write phase: lay down `codeFst`, `codeSnd` and the false marker leftwards. -/
theorem copyCells_write3 (a : Sym) (i : Nat) (hi : i < 4)
    (hiEq : i = 2 * bitOf (codeFst a) + bitOf (codeSnd a)) (L2 R : List Sym) :
    copyCells.run 3
      ⟨(⟨30 + i, by omega⟩ : Fin 128), Tape.mk (none :: none :: L2) (none :: R)⟩
      = ⟨(⟨42 + i, by omega⟩ : Fin 128),
          Tape.mk (codeFst a :: L2) (codeSnd a :: some false :: R)⟩ := by
  cases a with
  | none =>
      have h0 : i = 0 := by rw [hiEq]; simp [codeFst, codeSnd, symCode, bitOf]
      subst h0
      simpa only [codeFst, codeSnd, symCode, List.headD_cons, List.drop_zero,
        List.drop_succ_cons] using copyCells_write3_0 L2 R
  | some b => cases b with
    | false =>
        have h1 : i = 1 := by rw [hiEq]; simp [codeFst, codeSnd, symCode, bitOf]
        subst h1
        simpa only [codeFst, codeSnd, symCode, List.headD_cons, List.drop_zero,
          List.drop_succ_cons] using copyCells_write3_1 L2 R
    | true =>
        have h3 : i = 3 := by rw [hiEq]; simp [codeFst, codeSnd, symCode, bitOf]
        subst h3
        simpa only [codeFst, codeSnd, symCode, List.headD_cons, List.drop_zero,
          List.drop_succ_cons] using copyCells_write3_3 L2 R


/-! ### 回扫段（50..61 → 10/99） -/

/-- **回扫段：单格三步**：读两位编码、标记位为 `false` 时回到出发状态。
    One scanned cell: two code symbols plus a consumed (`false`) marker. -/
theorem copyCells_scanOne (q q1 q2 : Nat) (hq : q < 128) (hq1 : q1 < 128) (hq2 : q2 < 128)
    (hne : q ≠ 99) (hne1 : q1 ≠ 99) (hne2 : q2 ≠ 99)
    (s1 : ∀ b : Bool, copyCells.step ⟨q, hq⟩ (some b) = (⟨q1, hq1⟩, some b, Dir.right))
    (s2 : ∀ b : Bool, copyCells.step ⟨q1, hq1⟩ (some b) = (⟨q2, hq2⟩, some b, Dir.right))
    (s3 : copyCells.step ⟨q2, hq2⟩ (some false) = (⟨q, hq⟩, some false, Dir.right))
    (b1 b2 : Bool) (L tail : List Sym) :
    copyCells.run 3
      ⟨⟨q, hq⟩, Tape.mk L (some b1 :: some b2 :: some false :: tail)⟩
      = ⟨⟨q, hq⟩, Tape.mk (some false :: some b2 :: some b1 :: L) tail⟩ := by
  rw [show (3 : Nat) = 1 + (1 + 1) from rfl]
  rw [DTM.run_add copyCells 1 (1 + 1)]
  rw [estepC q hq (some b1) ⟨q1, hq1⟩ (some b1) Dir.right (s1 b1) L
    (some b2 :: some false :: tail) hne]
  etape
  rw [DTM.run_add copyCells 1 1]
  rw [estepC q1 hq1 (some b2) ⟨q2, hq2⟩ (some b2) Dir.right (s2 b2)
    (some b1 :: L) (some false :: tail) hne1]
  etape
  rw [estepC q2 hq2 (some false) ⟨q, hq⟩ (some false) Dir.right s3
    (some b2 :: some b1 :: L) tail hne2]
  etape

/-- **回扫段（通用循环）**：状态 `q`（50..53）自「整格序列 + 下一个未读格」的起点右行，
    每格三步，标记位 `false` 的格继续、`true` 的格转 `acc` 停。
    Generic right-scan loop over consumed cells (marker `false`), then one unread cell. -/
theorem copyCells_scanGen (q q1 q2 : Nat) (hq : q < 128) (hq1 : q1 < 128) (hq2 : q2 < 128)
    (hne : q ≠ 99) (hne1 : q1 ≠ 99) (hne2 : q2 ≠ 99) (acc : Fin 128)
    (s1 : ∀ b : Bool, copyCells.step ⟨q, hq⟩ (some b) = (⟨q1, hq1⟩, some b, Dir.right))
    (s2 : ∀ b : Bool, copyCells.step ⟨q1, hq1⟩ (some b) = (⟨q2, hq2⟩, some b, Dir.right))
    (s3 : copyCells.step ⟨q2, hq2⟩ (some false) = (⟨q, hq⟩, some false, Dir.right))
    (s4 : copyCells.step ⟨q2, hq2⟩ (some true) = (acc, some true, Dir.stay)) :
    ∀ (cs : List (Sym × Bool)), (∀ p ∈ cs, p.2 = false) → ∀ (b1 b2 : Bool) (L tail : List Sym),
      copyCells.run (3 * cs.length + 3)
        ⟨⟨q, hq⟩, Tape.mk L (codeCells cs ++ some b1 :: some b2 :: some true :: tail)⟩
      = ⟨acc, Tape.mk (some b2 :: some b1 :: (codeCells cs).reverse ++ L)
          (some true :: tail)⟩
  | [], _, b1, b2, L, tail => by
      simp only [codeCells, List.flatMap_nil, List.nil_append, List.reverse_nil]
      rw [show (3 * ([] : List (Sym × Bool)).length + 3 : Nat) = 1 + (1 + 1) from rfl]
      rw [DTM.run_add copyCells 1 (1 + 1)]
      rw [estepC q hq (some b1) ⟨q1, hq1⟩ (some b1) Dir.right (s1 b1) L
        (some b2 :: some true :: tail) hne]
      etape
      rw [DTM.run_add copyCells 1 1]
      rw [estepC q1 hq1 (some b2) ⟨q2, hq2⟩ (some b2) Dir.right (s2 b2)
        (some b1 :: L) (some true :: tail) hne1]
      etape
      rw [estepC q2 hq2 (some true) acc (some true) Dir.stay s4
        (some b2 :: some b1 :: L) tail hne2]
      etape
  | (c, m) :: ps, hcs, b1, b2, L, tail => by
      have hm : m = false := hcs (c, m) (by simp)
      subst hm
      rw [show (3 * ((c, false) :: ps).length + 3 : Nat) = 3 + (3 * ps.length + 3) from by
            simp only [List.length_cons]; omega]
      rw [DTM.run_add copyCells 3 (3 * ps.length + 3)]
      -- 单格三步（`scanOne`），按内容分三支后交归纳假设
      have hrec := copyCells_scanGen q q1 q2 hq hq1 hq2 hne hne1 hne2 acc s1 s2 s3 s4 ps
        (by intro p hp; exact hcs p (List.mem_cons_of_mem _ hp)) b1 b2
      cases c with
      | none =>
          rw [show copyCells.run 3
                ⟨⟨q, hq⟩, Tape.mk L (codeCells ((none, false) :: ps) ++ some b1 :: some b2 ::
                  some true :: tail)⟩
              = ⟨⟨q, hq⟩, Tape.mk (some false :: some false :: some false :: L)
                  (codeCells ps ++ some b1 :: some b2 :: some true :: tail)⟩ from by
                simpa only [codeCells_cons, cellCode, symCode, codeFst, codeSnd, Bool.false_eq_true, ite_false,
                  List.headD_cons, List.drop_zero, List.drop_succ_cons, List.nil_append,
                  List.cons_append, List.singleton_append] using
                  copyCells_scanOne q q1 q2 hq hq1 hq2 hne hne1 hne2 s1 s2 s3 false false L
                    (codeCells ps ++ some b1 :: some b2 :: some true :: tail)]
          rw [hrec (some false :: some false :: some false :: L) tail]
          simp only [codeCells_cons, cellCode, symCode, Bool.false_eq_true, ite_false,
            List.nil_append, List.reverse_cons, List.append_assoc, List.cons_append]
      | some b => cases b with
        | false =>
            rw [show copyCells.run 3
                  ⟨⟨q, hq⟩, Tape.mk L (codeCells ((some false, false) :: ps) ++ some b1 ::
                    some b2 :: some true :: tail)⟩
                = ⟨⟨q, hq⟩, Tape.mk (some false :: some true :: some false :: L)
                    (codeCells ps ++ some b1 :: some b2 :: some true :: tail)⟩ from by
                  simpa only [codeCells_cons, cellCode, symCode, codeFst, codeSnd, Bool.false_eq_true, ite_false,
                    List.headD_cons, List.drop_zero, List.drop_succ_cons, List.nil_append,
                    List.cons_append, List.singleton_append] using
                    copyCells_scanOne q q1 q2 hq hq1 hq2 hne hne1 hne2 s1 s2 s3 false true L
                      (codeCells ps ++ some b1 :: some b2 :: some true :: tail)]
            rw [hrec (some false :: some true :: some false :: L) tail]
            simp only [codeCells_cons, cellCode, symCode, Bool.false_eq_true, ite_false,
              List.nil_append, List.reverse_cons, List.append_assoc, List.cons_append]
        | true =>
            rw [show copyCells.run 3
                  ⟨⟨q, hq⟩, Tape.mk L (codeCells ((some true, false) :: ps) ++ some b1 ::
                    some b2 :: some true :: tail)⟩
                = ⟨⟨q, hq⟩, Tape.mk (some false :: some true :: some true :: L)
                    (codeCells ps ++ some b1 :: some b2 :: some true :: tail)⟩ from by
                  simpa only [codeCells_cons, cellCode, symCode, codeFst, codeSnd, Bool.false_eq_true, ite_false,
                    List.headD_cons, List.drop_zero, List.drop_succ_cons, List.nil_append,
                    List.cons_append, List.singleton_append] using
                    copyCells_scanOne q q1 q2 hq hq1 hq2 hne hne1 hne2 s1 s2 s3 true true L
                      (codeCells ps ++ some b1 :: some b2 :: some true :: tail)]
            rw [hrec (some false :: some true :: some true :: L) tail]
            simp only [codeCells_cons, cellCode, symCode, Bool.false_eq_true, ite_false,
              List.nil_append, List.reverse_cons, List.append_assoc, List.cons_append]

/-- 回扫段（`i = 0`）：`50 → 54 → 58 → 10`。 Scan phase starting at state 50. -/
theorem copyCells_scan0 :
    ∀ (cs : List (Sym × Bool)), (∀ p ∈ cs, p.2 = false) → ∀ (b1 b2 : Bool) (L tail : List Sym),
      copyCells.run (3 * cs.length + 3)
        ⟨(⟨50, by omega⟩ : Fin 128),
          Tape.mk L (codeCells cs ++ some b1 :: some b2 :: some true :: tail)⟩
      = ⟨(⟨10, by omega⟩ : Fin 128),
          Tape.mk (some b2 :: some b1 :: (codeCells cs).reverse ++ L) (some true :: tail)⟩ :=
  copyCells_scanGen 50 54 58 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ⟨10, by omega⟩ (by intro b; cases b <;> rfl) (by intro b; cases b <;> rfl)
    (by rfl) (by rfl)

/-- 回扫段（`i = 1`）：`51 → 55 → 59 → 10`。 -/
theorem copyCells_scan1 :
    ∀ (cs : List (Sym × Bool)), (∀ p ∈ cs, p.2 = false) → ∀ (b1 b2 : Bool) (L tail : List Sym),
      copyCells.run (3 * cs.length + 3)
        ⟨(⟨51, by omega⟩ : Fin 128),
          Tape.mk L (codeCells cs ++ some b1 :: some b2 :: some true :: tail)⟩
      = ⟨(⟨10, by omega⟩ : Fin 128),
          Tape.mk (some b2 :: some b1 :: (codeCells cs).reverse ++ L) (some true :: tail)⟩ :=
  copyCells_scanGen 51 55 59 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ⟨10, by omega⟩ (by intro b; cases b <;> rfl) (by intro b; cases b <;> rfl)
    (by rfl) (by rfl)

/-- 回扫段（`i = 2`）：`52 → 56 → 60 → 10`。 -/
theorem copyCells_scan2 :
    ∀ (cs : List (Sym × Bool)), (∀ p ∈ cs, p.2 = false) → ∀ (b1 b2 : Bool) (L tail : List Sym),
      copyCells.run (3 * cs.length + 3)
        ⟨(⟨52, by omega⟩ : Fin 128),
          Tape.mk L (codeCells cs ++ some b1 :: some b2 :: some true :: tail)⟩
      = ⟨(⟨10, by omega⟩ : Fin 128),
          Tape.mk (some b2 :: some b1 :: (codeCells cs).reverse ++ L) (some true :: tail)⟩ :=
  copyCells_scanGen 52 56 60 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ⟨10, by omega⟩ (by intro b; cases b <;> rfl) (by intro b; cases b <;> rfl)
    (by rfl) (by rfl)

/-- 回扫段（`i = 3`）：`53 → 57 → 61 → 10`。 -/
theorem copyCells_scan3 :
    ∀ (cs : List (Sym × Bool)), (∀ p ∈ cs, p.2 = false) → ∀ (b1 b2 : Bool) (L tail : List Sym),
      copyCells.run (3 * cs.length + 3)
        ⟨(⟨53, by omega⟩ : Fin 128),
          Tape.mk L (codeCells cs ++ some b1 :: some b2 :: some true :: tail)⟩
      = ⟨(⟨10, by omega⟩ : Fin 128),
          Tape.mk (some b2 :: some b1 :: (codeCells cs).reverse ++ L) (some true :: tail)⟩ :=
  copyCells_scanGen 53 57 61 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ⟨10, by omega⟩ (by intro b; cases b <;> rfl) (by intro b; cases b <;> rfl)
    (by rfl) (by rfl)

/-- **回扫段**：状态 `50 + i`（`i < 4`）扫过已消费整格，停在下一个标记位 `true` 上转 `10`。
    The scan phase for any `i < 4`. -/
theorem copyCells_scan (i : Nat) (hi : i < 4) :
    ∀ (cs : List (Sym × Bool)), (∀ p ∈ cs, p.2 = false) → ∀ (b1 b2 : Bool) (L tail : List Sym),
      copyCells.run (3 * cs.length + 3)
        ⟨(⟨50 + i, by omega⟩ : Fin 128),
          Tape.mk L (codeCells cs ++ some b1 :: some b2 :: some true :: tail)⟩
      = ⟨(⟨10, by omega⟩ : Fin 128),
          Tape.mk (some b2 :: some b1 :: (codeCells cs).reverse ++ L) (some true :: tail)⟩ := by
  rcases nat_lt4_cases hi with h | h | h | h
  · subst h; exact copyCells_scan0
  · subst h; exact copyCells_scan1
  · subst h; exact copyCells_scan2
  · subst h; exact copyCells_scan3

/-- **末轮回扫（通用循环）**：区域右侧是空白（源块已读完）。扫过全部整格（每格 3 步）后
    读空白转 `acc` 停机，左侧带累积区域逆序。
    Final-round scan: cells then a blank; the blank halts into `acc`. -/
theorem copyCells_scanEndGen (q q1 q2 : Nat) (hq : q < 128) (hq1 : q1 < 128) (hq2 : q2 < 128)
    (hne : q ≠ 99) (hne1 : q1 ≠ 99) (hne2 : q2 ≠ 99) (acc : Fin 128)
    (s1 : ∀ b : Bool, copyCells.step ⟨q, hq⟩ (some b) = (⟨q1, hq1⟩, some b, Dir.right))
    (s2 : ∀ b : Bool, copyCells.step ⟨q1, hq1⟩ (some b) = (⟨q2, hq2⟩, some b, Dir.right))
    (s3 : copyCells.step ⟨q2, hq2⟩ (some false) = (⟨q, hq⟩, some false, Dir.right))
    (s4 : copyCells.step ⟨q, hq⟩ none = (acc, none, Dir.stay)) :
    ∀ (cs : List (Sym × Bool)), (∀ p ∈ cs, p.2 = false) → ∀ (L tail : List Sym),
      copyCells.run (3 * cs.length + 1)
        ⟨⟨q, hq⟩, Tape.mk L (codeCells cs ++ none :: tail)⟩
      = ⟨acc, Tape.mk ((codeCells cs).reverse ++ L) (none :: tail)⟩
  | [], _, L, tail => by
      simp only [codeCells, List.flatMap_nil, List.nil_append, List.reverse_nil]
      rw [show (3 * ([] : List (Sym × Bool)).length + 1 : Nat) = 1 from rfl]
      rw [estepC q hq none acc none Dir.stay s4 L tail hne]
      etape
  | (c, m) :: ps, hcs, L, tail => by
      have hm : m = false := hcs (c, m) (by simp)
      subst hm
      rw [show (3 * ((c, false) :: ps).length + 1 : Nat) = 3 + (3 * ps.length + 1) from by
            simp only [List.length_cons]; omega]
      rw [DTM.run_add copyCells 3 (3 * ps.length + 1)]
      -- 单格三步（`scanOne`），按内容分三支后交归纳假设
      have hrec := copyCells_scanEndGen q q1 q2 hq hq1 hq2 hne hne1 hne2 acc s1 s2 s3 s4 ps
        (by intro p hp; exact hcs p (List.mem_cons_of_mem _ hp))
      cases c with
      | none =>
          rw [show copyCells.run 3
                ⟨⟨q, hq⟩, Tape.mk L (codeCells ((none, false) :: ps) ++ none :: tail)⟩
              = ⟨⟨q, hq⟩, Tape.mk (some false :: some false :: some false :: L)
                  (codeCells ps ++ none :: tail)⟩ from by
                simpa only [codeCells_cons, cellCode, symCode, codeFst, codeSnd, Bool.false_eq_true, ite_false,
                  List.headD_cons, List.drop_zero, List.drop_succ_cons, List.nil_append,
                  List.cons_append, List.singleton_append] using
                  copyCells_scanOne q q1 q2 hq hq1 hq2 hne hne1 hne2 s1 s2 s3 false false L
                    (codeCells ps ++ none :: tail)]
          rw [hrec (some false :: some false :: some false :: L) tail]
          simp only [codeCells_cons, cellCode, symCode, Bool.false_eq_true, ite_false,
            List.nil_append, List.reverse_cons, List.append_assoc, List.cons_append]
      | some b => cases b with
        | false =>
            rw [show copyCells.run 3
                  ⟨⟨q, hq⟩, Tape.mk L (codeCells ((some false, false) :: ps) ++ none :: tail)⟩
                = ⟨⟨q, hq⟩, Tape.mk (some false :: some true :: some false :: L)
                    (codeCells ps ++ none :: tail)⟩ from by
                  simpa only [codeCells_cons, cellCode, symCode, codeFst, codeSnd, Bool.false_eq_true,
                    ite_false, List.headD_cons, List.drop_zero, List.drop_succ_cons, List.nil_append,
                    List.cons_append, List.singleton_append] using
                    copyCells_scanOne q q1 q2 hq hq1 hq2 hne hne1 hne2 s1 s2 s3 false true L
                      (codeCells ps ++ none :: tail)]
            rw [hrec (some false :: some true :: some false :: L) tail]
            simp only [codeCells_cons, cellCode, symCode, Bool.false_eq_true, ite_false,
              List.nil_append, List.reverse_cons, List.append_assoc, List.cons_append]
        | true =>
            rw [show copyCells.run 3
                  ⟨⟨q, hq⟩, Tape.mk L (codeCells ((some true, false) :: ps) ++ none :: tail)⟩
                = ⟨⟨q, hq⟩, Tape.mk (some false :: some true :: some true :: L)
                    (codeCells ps ++ none :: tail)⟩ from by
                  simpa only [codeCells_cons, cellCode, symCode, codeFst, codeSnd, Bool.false_eq_true,
                    ite_false, List.headD_cons, List.drop_zero, List.drop_succ_cons, List.nil_append,
                    List.cons_append, List.singleton_append] using
                    copyCells_scanOne q q1 q2 hq hq1 hq2 hne hne1 hne2 s1 s2 s3 true true L
                      (codeCells ps ++ none :: tail)]
            rw [hrec (some false :: some true :: some true :: L) tail]
            simp only [codeCells_cons, cellCode, symCode, Bool.false_eq_true, ite_false,
              List.nil_append, List.reverse_cons, List.append_assoc, List.cons_append]

/-- 末轮回扫（`i = 0`）：`50 → 54 → 58`，读空白转 `99`。 -/
theorem copyCells_scanEnd0 :
    ∀ (cs : List (Sym × Bool)), (∀ p ∈ cs, p.2 = false) → ∀ (L tail : List Sym),
      copyCells.run (3 * cs.length + 1)
        ⟨(⟨50, by omega⟩ : Fin 128), Tape.mk L (codeCells cs ++ none :: tail)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk ((codeCells cs).reverse ++ L) (none :: tail)⟩ :=
  copyCells_scanEndGen 50 54 58 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ⟨99, by omega⟩ (by intro b; cases b <;> rfl) (by intro b; cases b <;> rfl)
    (by rfl) (by rfl)

/-- 末轮回扫（`i = 1`）：`51 → 55 → 59`，读空白转 `99`。 -/
theorem copyCells_scanEnd1 :
    ∀ (cs : List (Sym × Bool)), (∀ p ∈ cs, p.2 = false) → ∀ (L tail : List Sym),
      copyCells.run (3 * cs.length + 1)
        ⟨(⟨51, by omega⟩ : Fin 128), Tape.mk L (codeCells cs ++ none :: tail)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk ((codeCells cs).reverse ++ L) (none :: tail)⟩ :=
  copyCells_scanEndGen 51 55 59 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ⟨99, by omega⟩ (by intro b; cases b <;> rfl) (by intro b; cases b <;> rfl)
    (by rfl) (by rfl)

/-- 末轮回扫（`i = 2`）：`52 → 56 → 60`，读空白转 `99`。 -/
theorem copyCells_scanEnd2 :
    ∀ (cs : List (Sym × Bool)), (∀ p ∈ cs, p.2 = false) → ∀ (L tail : List Sym),
      copyCells.run (3 * cs.length + 1)
        ⟨(⟨52, by omega⟩ : Fin 128), Tape.mk L (codeCells cs ++ none :: tail)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk ((codeCells cs).reverse ++ L) (none :: tail)⟩ :=
  copyCells_scanEndGen 52 56 60 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ⟨99, by omega⟩ (by intro b; cases b <;> rfl) (by intro b; cases b <;> rfl)
    (by rfl) (by rfl)

/-- 末轮回扫（`i = 3`）：`53 → 57 → 61`，读空白转 `99`。 -/
theorem copyCells_scanEnd3 :
    ∀ (cs : List (Sym × Bool)), (∀ p ∈ cs, p.2 = false) → ∀ (L tail : List Sym),
      copyCells.run (3 * cs.length + 1)
        ⟨(⟨53, by omega⟩ : Fin 128), Tape.mk L (codeCells cs ++ none :: tail)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk ((codeCells cs).reverse ++ L) (none :: tail)⟩ :=
  copyCells_scanEndGen 53 57 61 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    ⟨99, by omega⟩ (by intro b; cases b <;> rfl) (by intro b; cases b <;> rfl)
    (by rfl) (by rfl)

/-- **末轮回扫**：状态 `50 + i`（`i < 4`）扫过全部整格后遇空白转 `99`，成本 `3|cs| + 1`。
    The final round's scan for any `i < 4`. -/
theorem copyCells_scanEnd (i : Nat) (hi : i < 4) :
    ∀ (cs : List (Sym × Bool)), (∀ p ∈ cs, p.2 = false) → ∀ (L tail : List Sym),
      copyCells.run (3 * cs.length + 1)
        ⟨(⟨50 + i, by omega⟩ : Fin 128), Tape.mk L (codeCells cs ++ none :: tail)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk ((codeCells cs).reverse ++ L) (none :: tail)⟩ := by
  rcases nat_lt4_cases hi with h | h | h | h
  · subst h; exact copyCells_scanEnd0
  · subst h; exact copyCells_scanEnd1
  · subst h; exact copyCells_scanEnd2
  · subst h; exact copyCells_scanEnd3

/-! ### 一轮合成（读格 + 走左 + 写格 + 回右 + 回扫） -/

/-- **回右两格（通用）**：两步右行，符号压进左带。
    Two right moves; symbols accumulate on the left tape. -/
theorem copyCells_back2 (q q4 q8 : Nat) (hq : q < 128) (hq4 : q4 < 128) (hq8 : q8 < 128)
    (hne : q ≠ 99) (hne4 : q4 ≠ 99)
    (s1 : ∀ a : Sym, copyCells.step ⟨q, hq⟩ a = (⟨q4, hq4⟩, a, Dir.right))
    (s2 : ∀ a : Sym, copyCells.step ⟨q4, hq4⟩ a = (⟨q8, hq8⟩, a, Dir.right)) :
    ∀ (x y : Sym) (M R : List Sym),
      copyCells.run 2 ⟨⟨q, hq⟩, Tape.mk M (x :: y :: R)⟩
        = ⟨⟨q8, hq8⟩, Tape.mk (y :: x :: M) R⟩ := by
  intro x y M R
  rw [show (2 : Nat) = 1 + 1 from rfl]
  rw [DTM.run_add copyCells 1 1]
  rw [estepC q hq x ⟨q4, hq4⟩ x Dir.right (s1 x) M (y :: R) hne]
  etape
  rw [estepC q4 hq4 y ⟨q8, hq8⟩ y Dir.right (s2 y) (x :: M) R hne4]
  etape

/-- 回右两格（`i = 0`）：`42 → 46 → 50`。 -/
theorem copyCells_back2_42 :
    ∀ (x y : Sym) (M R : List Sym),
      copyCells.run 2 ⟨(⟨42, by omega⟩ : Fin 128), Tape.mk M (x :: y :: R)⟩
        = ⟨(⟨50, by omega⟩ : Fin 128), Tape.mk (y :: x :: M) R⟩ :=
  copyCells_back2 42 46 50 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by intro a; rfl) (by intro a; rfl)

/-- 回右两格（`i = 1`）：`43 → 47 → 51`。 -/
theorem copyCells_back2_43 :
    ∀ (x y : Sym) (M R : List Sym),
      copyCells.run 2 ⟨(⟨43, by omega⟩ : Fin 128), Tape.mk M (x :: y :: R)⟩
        = ⟨(⟨51, by omega⟩ : Fin 128), Tape.mk (y :: x :: M) R⟩ :=
  copyCells_back2 43 47 51 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by intro a; rfl) (by intro a; rfl)

/-- 回右两格（`i = 2`）：`44 → 48 → 52`。 -/
theorem copyCells_back2_44 :
    ∀ (x y : Sym) (M R : List Sym),
      copyCells.run 2 ⟨(⟨44, by omega⟩ : Fin 128), Tape.mk M (x :: y :: R)⟩
        = ⟨(⟨52, by omega⟩ : Fin 128), Tape.mk (y :: x :: M) R⟩ :=
  copyCells_back2 44 48 52 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by intro a; rfl) (by intro a; rfl)

/-- 回右两格（`i = 3`）：`45 → 49 → 53`。 -/
theorem copyCells_back2_45 :
    ∀ (x y : Sym) (M R : List Sym),
      copyCells.run 2 ⟨(⟨45, by omega⟩ : Fin 128), Tape.mk M (x :: y :: R)⟩
        = ⟨(⟨53, by omega⟩ : Fin 128), Tape.mk (y :: x :: M) R⟩ :=
  copyCells_back2 45 49 53 (by omega) (by omega) (by omega) (by omega) (by omega)
    (by intro a; rfl) (by intro a; rfl)

/-- 回右两格（`42 + i`，`i < 4`）。 Two right moves from `42 + i`. -/
theorem copyCells_back2' (i : Nat) (hi : i < 4) :
    ∀ (x y : Sym) (M R : List Sym),
      copyCells.run 2 ⟨(⟨42 + i, by omega⟩ : Fin 128), Tape.mk M (x :: y :: R)⟩
        = ⟨(⟨50 + i, by omega⟩ : Fin 128), Tape.mk (y :: x :: M) R⟩ := by
  rcases nat_lt4_cases hi with h | h | h | h
  · subst h; exact copyCells_back2_42
  · subst h; exact copyCells_back2_43
  · subst h; exact copyCells_back2_44
  · subst h; exact copyCells_back2_45

/-- 停留步（通用）：状态 `q` 读到空白后原地停转 `q'`，纸带不动。
    A stay step on a blank (generic). -/
theorem copyCells_stayStep (q q' : Nat) (hq : q < 128) (hq' : q' < 128) (hne : q ≠ 99)
    (h : copyCells.step ⟨q, hq⟩ none = (⟨q', hq'⟩, none, Dir.stay)) (M R : List Sym) :
    copyCells.run 1 ⟨⟨q, hq⟩, Tape.mk M (none :: R)⟩
      = ⟨⟨q', hq'⟩, Tape.mk M (none :: R)⟩ := by
  rw [estepC q hq none ⟨q', hq'⟩ none Dir.stay h M R hne]
  etape

/-- 走左终止步（`20 + i`，`i < 4`）：读到空白即转入 `30 + i`，头与纸带不动。
    Blank-stop step for any `i < 4`. -/
theorem copyCells_walkStop (i : Nat) (hi : i < 4) :
    ∀ (M R : List Sym),
      copyCells.run 1 ⟨(⟨20 + i, by omega⟩ : Fin 128), Tape.mk M (none :: R)⟩
        = ⟨(⟨30 + i, by omega⟩ : Fin 128), Tape.mk M (none :: R)⟩ := by
  rcases nat_lt4_cases hi with h | h | h | h
  · subst h; exact copyCells_stayStep 20 30 (by omega) (by omega) (by omega) (by rfl)
  · subst h; exact copyCells_stayStep 21 31 (by omega) (by omega) (by omega) (by rfl)
  · subst h; exact copyCells_stayStep 22 32 (by omega) (by omega) (by omega) (by rfl)
  · subst h; exact copyCells_stayStep 23 33 (by omega) (by omega) (by omega) (by rfl)

/-- 区域末尾补一格后的编码展开（供回扫段匹配）。
    Appending one target cell to a region code list. -/
theorem codeCells_snoc_false (cs : List (Sym × Bool)) (a : Sym) (t : List Sym) :
    codeCells (cs ++ [(a, false)]) ++ t
      = codeCells cs ++ codeFst a :: codeSnd a :: some false :: t := by
  rw [codeCells_append, codeCells_pair_false, List.append_assoc]
  rfl

/-- 区域逆序串与末符号：`E'.reverse ++ 标记 :: Y = E.reverse ++ Y`（当 `E = 标记 :: E'`）。
    Region-reverse helper: `E'.reverse ++ marker :: Y = E.reverse ++ Y`. -/
theorem rev_cons_append (E E' : List Sym) (hE' : E = some false :: E') (Y : List Sym) :
    E'.reverse ++ some false :: Y = E.reverse ++ Y := by
  rw [hE', List.reverse_cons]
  simp only [List.singleton_append, List.append_assoc]

/-- **转写首轮**（区内为空、格左邻为空白）：读格 3 步、停 1 步、写镜像格 3 步、回右 2 步、
    回扫 6 步（扫过新写的镜像格），停在下一个源格标记位 `true` 上。
    First round (empty region, blank left neighbour): read, stop, write mirror, back, scan. -/
theorem copyCells_roundFirst (a : Sym) (b1 b2 : Bool) (tail L2 : List Sym) :
    copyCells.run 15
      ⟨(⟨10, by omega⟩ : Fin 128),
        Tape.mk (codeSnd a :: codeFst a :: none :: none :: none :: L2)
          (some true :: some b1 :: some b2 :: some true :: tail)⟩
      = ⟨(⟨10, by omega⟩ : Fin 128),
          Tape.mk (some b2 :: some b1 :: (codeCells [(a, false)]).reverse ++
              some false :: codeSnd a :: codeFst a :: L2)
            (some true :: tail)⟩ := by
  -- 状态码 `i = 2·b1' + b2'`
  have hi : 2 * bitOf (codeFst a) + bitOf (codeSnd a) < 4 := by
    have h1 := bitOf_le_one (codeFst a)
    have h2 := bitOf_le_one (codeSnd a)
    omega
  -- 分段：读 3 + 停 1 + 写 3 + 回 2 + 扫 (3·1+3)
  rw [show (15 : Nat) = 3 + (1 + (3 + (2 + (3 * [(a, false)].length + 3)))) from by simp]
  rw [DTM.run_add copyCells 3 (1 + (3 + (2 + (3 * [(a, false)].length + 3))))]
  rw [show copyCells.run 3
        ⟨(⟨10, by omega⟩ : Fin 128),
          Tape.mk (codeSnd a :: codeFst a :: none :: none :: none :: L2)
            (some true :: some b1 :: some b2 :: some true :: tail)⟩
      = ⟨(⟨20 + 2 * bitOf (codeFst a) + bitOf (codeSnd a), by omega⟩ : Fin 128),
          Tape.mk (none :: none :: L2)
            (none :: codeFst a :: codeSnd a :: some false ::
              some b1 :: some b2 :: some true :: tail)⟩
      from copyCells_read3 a none (none :: none :: L2)
        (some b1 :: some b2 :: some true :: tail)]
  -- 状态改写成 `20 + i` 的右结合形态
  rw [show (⟨20 + 2 * bitOf (codeFst a) + bitOf (codeSnd a), by omega⟩ : Fin 128)
        = (⟨20 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128)
      from Fin.ext (Nat.add_assoc 20 (2 * bitOf (codeFst a)) (bitOf (codeSnd a)))]
  rw [DTM.run_add copyCells 1 (3 + (2 + (3 * [(a, false)].length + 3)))]
  rw [show copyCells.run 1
        ⟨(⟨20 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (none :: none :: L2)
            (none :: codeFst a :: codeSnd a :: some false ::
              some b1 :: some b2 :: some true :: tail)⟩
      = ⟨(⟨30 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (none :: none :: L2)
            (none :: codeFst a :: codeSnd a :: some false ::
              some b1 :: some b2 :: some true :: tail)⟩
      from copyCells_walkStop (2 * bitOf (codeFst a) + bitOf (codeSnd a)) hi
        (none :: none :: L2)
        (codeFst a :: codeSnd a :: some false :: some b1 :: some b2 :: some true :: tail)]
  rw [DTM.run_add copyCells 3 (2 + (3 * [(a, false)].length + 3))]
  rw [show copyCells.run 3
        ⟨(⟨30 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (none :: none :: L2)
            (none :: codeFst a :: codeSnd a :: some false ::
              some b1 :: some b2 :: some true :: tail)⟩
      = ⟨(⟨42 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (codeFst a :: L2)
            (codeSnd a :: some false :: codeFst a :: codeSnd a :: some false ::
              some b1 :: some b2 :: some true :: tail)⟩
      from copyCells_write3 a (2 * bitOf (codeFst a) + bitOf (codeSnd a)) hi rfl L2
        (codeFst a :: codeSnd a :: some false :: some b1 :: some b2 :: some true :: tail)]
  rw [DTM.run_add copyCells 2 (3 * [(a, false)].length + 3)]
  rw [show copyCells.run 2
        ⟨(⟨42 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (codeFst a :: L2)
            (codeSnd a :: some false :: codeFst a :: codeSnd a :: some false ::
              some b1 :: some b2 :: some true :: tail)⟩
      = ⟨(⟨50 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (some false :: codeSnd a :: codeFst a :: L2)
            (codeFst a :: codeSnd a :: some false ::
              some b1 :: some b2 :: some true :: tail)⟩
      from copyCells_back2' (2 * bitOf (codeFst a) + bitOf (codeSnd a)) hi (codeSnd a) (some false)
        (codeFst a :: L2)
        (codeFst a :: codeSnd a :: some false :: some b1 :: some b2 :: some true :: tail)]
  -- 新镜像格的编码并入回扫段匹配形态
  rw [show codeFst a :: codeSnd a :: some false :: some b1 :: some b2 :: some true :: tail
        = codeCells [(a, false)] ++ some b1 :: some b2 :: some true :: tail from
    (codeCells_snoc_false [] a (some b1 :: some b2 :: some true :: tail)).symm]
  rw [show copyCells.run (3 * [(a, false)].length + 3)
        ⟨(⟨50 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (some false :: codeSnd a :: codeFst a :: L2)
            (codeCells [(a, false)] ++ some b1 :: some b2 :: some true :: tail)⟩
      = ⟨(⟨10, by omega⟩ : Fin 128),
          Tape.mk (some b2 :: some b1 :: (codeCells [(a, false)]).reverse ++
              some false :: codeSnd a :: codeFst a :: L2)
            (some true :: tail)⟩
      from copyCells_scan (2 * bitOf (codeFst a) + bitOf (codeSnd a)) hi [(a, false)]
        (by intro q hq; simp only [List.mem_singleton] at hq; rw [hq]) b1 b2
        (some false :: codeSnd a :: codeFst a :: L2) tail]

/-- **转写一轮**（区内非空）：区域逆序串写作 `E = some false :: E'`。读格 3 步、跨过 `E'`
    （`|E'| + 2` 步）、左向写镜像格 3 步、回右 2 步、扫过区域与原格（`3(|cs|+1) + 3` 步），
    停在下一个源格标记位上。
    One round over a non-empty region whose symbol-reverse is `E = some false :: E'`. -/
theorem copyCells_round (a : Sym) (cs : List (Sym × Bool)) (hcs : ∀ p ∈ cs, p.2 = false)
    (E E' : List Sym) (hE : E = (codeCells cs).reverse) (hE' : E = some false :: E')
    (b1 b2 : Bool) (tail L2 : List Sym) :
    copyCells.run (3 + (E'.length + 2) + 3 + 2 + (3 * (cs.length + 1) + 3))
      ⟨(⟨10, by omega⟩ : Fin 128),
        Tape.mk (codeSnd a :: codeFst a :: (E ++ none :: none :: none :: L2))
          (some true :: some b1 :: some b2 :: some true :: tail)⟩
      = ⟨(⟨10, by omega⟩ : Fin 128),
          Tape.mk (some b2 :: some b1 :: (codeCells (cs ++ [(a, false)])).reverse ++
              some false :: codeSnd a :: codeFst a :: L2)
            (some true :: tail)⟩ := by
  -- 走左段前提：`E'` 的符号都是编码符号（非空白）
  have hl : ∀ y ∈ E', y ≠ none := by
    intro y hy
    have hyE : y ∈ E := by rw [hE']; exact List.mem_cons_of_mem _ hy
    rw [hE] at hyE
    exact codeCells_ne_none cs y (List.mem_reverse.mp hyE)
  -- 状态码 `i = 2·b1' + b2'`
  have hi : 2 * bitOf (codeFst a) + bitOf (codeSnd a) < 4 := by
    have h1 := bitOf_le_one (codeFst a)
    have h2 := bitOf_le_one (codeSnd a)
    omega
  -- 分段：读 3 + 走 (|E'|+2) + 写 3 + 回 2 + 扫 (3(|cs|+1)+3)
  rw [show 3 + (E'.length + 2) + 3 + 2 + (3 * (cs.length + 1) + 3)
        = 3 + ((E'.length + 2) + (3 + (2 + (3 * (cs.length + 1) + 3)))) from by omega]
  rw [hE']
  simp only [List.cons_append]
  rw [DTM.run_add copyCells 3 ((E'.length + 2) + (3 + (2 + (3 * (cs.length + 1) + 3))))]
  rw [show copyCells.run 3
        ⟨(⟨10, by omega⟩ : Fin 128),
          Tape.mk (codeSnd a :: codeFst a :: some false ::
              (E' ++ none :: none :: none :: L2))
            (some true :: some b1 :: some b2 :: some true :: tail)⟩
      = ⟨(⟨20 + 2 * bitOf (codeFst a) + bitOf (codeSnd a), by omega⟩ : Fin 128),
          Tape.mk (E' ++ none :: none :: none :: L2)
            (some false :: codeFst a :: codeSnd a :: some false ::
              some b1 :: some b2 :: some true :: tail)⟩
      from copyCells_read3 a (some false) (E' ++ none :: none :: none :: L2)
        (some b1 :: some b2 :: some true :: tail)]
  rw [show (⟨20 + 2 * bitOf (codeFst a) + bitOf (codeSnd a), by omega⟩ : Fin 128)
        = (⟨20 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128)
      from Fin.ext (Nat.add_assoc 20 (2 * bitOf (codeFst a)) (bitOf (codeSnd a)))]
  rw [DTM.run_add copyCells (E'.length + 2) (3 + (2 + (3 * (cs.length + 1) + 3)))]
  rw [show copyCells.run (E'.length + 2)
        ⟨(⟨20 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (E' ++ none :: none :: none :: L2)
            (some false :: codeFst a :: codeSnd a :: some false ::
              some b1 :: some b2 :: some true :: tail)⟩
      = ⟨(⟨30 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (none :: none :: L2)
            (none :: E'.reverse ++ some false :: codeFst a :: codeSnd a :: some false ::
              some b1 :: some b2 :: some true :: tail)⟩
      from copyCells_walkL (2 * bitOf (codeFst a) + bitOf (codeSnd a)) hi E' hl false
        (none :: none :: L2)
        (codeFst a :: codeSnd a :: some false :: some b1 :: some b2 :: some true :: tail)]
  rw [DTM.run_add copyCells 3 (2 + (3 * (cs.length + 1) + 3))]
  rw [show copyCells.run 3
        ⟨(⟨30 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (none :: none :: L2)
            (none :: E'.reverse ++ some false :: codeFst a :: codeSnd a :: some false ::
              some b1 :: some b2 :: some true :: tail)⟩
      = ⟨(⟨42 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (codeFst a :: L2)
            (codeSnd a :: some false :: E'.reverse ++ some false :: codeFst a :: codeSnd a ::
              some false :: some b1 :: some b2 :: some true :: tail)⟩
      from copyCells_write3 a (2 * bitOf (codeFst a) + bitOf (codeSnd a)) hi rfl L2
        (E'.reverse ++ some false :: codeFst a :: codeSnd a :: some false ::
          some b1 :: some b2 :: some true :: tail)]
  rw [DTM.run_add copyCells 2 (3 * (cs.length + 1) + 3)]
  rw [show copyCells.run 2
        ⟨(⟨42 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (codeFst a :: L2)
            (codeSnd a :: some false :: E'.reverse ++ some false :: codeFst a :: codeSnd a ::
              some false :: some b1 :: some b2 :: some true :: tail)⟩
      = ⟨(⟨50 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (some false :: codeSnd a :: codeFst a :: L2)
            (E'.reverse ++ some false :: codeFst a :: codeSnd a :: some false ::
              some b1 :: some b2 :: some true :: tail)⟩
      from copyCells_back2' (2 * bitOf (codeFst a) + bitOf (codeSnd a)) hi (codeSnd a) (some false)
        (codeFst a :: L2)
        (E'.reverse ++ some false :: codeFst a :: codeSnd a :: some false ::
          some b1 :: some b2 :: some true :: tail)]
  -- 区域逆序串还原成区域编码，再并上新格编码（供回扫段匹配）
  rw [show E'.reverse ++ some false :: codeFst a :: codeSnd a :: some false ::
        some b1 :: some b2 :: some true :: tail
      = codeCells (cs ++ [(a, false)]) ++ some b1 :: some b2 :: some true :: tail from by
    rw [rev_cons_append E E' hE' (codeFst a :: codeSnd a :: some false ::
      some b1 :: some b2 :: some true :: tail)]
    rw [hE, List.reverse_reverse]
    exact (codeCells_snoc_false cs a (some b1 :: some b2 :: some true :: tail)).symm]
  rw [show (3 * (cs.length + 1) + 3) = 3 * (cs ++ [(a, false)]).length + 3 from by
    simp]
  rw [show copyCells.run (3 * (cs ++ [(a, false)]).length + 3)
        ⟨(⟨50 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (some false :: codeSnd a :: codeFst a :: L2)
            (codeCells (cs ++ [(a, false)]) ++ some b1 :: some b2 :: some true :: tail)⟩
      = ⟨(⟨10, by omega⟩ : Fin 128),
          Tape.mk (some b2 :: some b1 :: (codeCells (cs ++ [(a, false)])).reverse ++
              some false :: codeSnd a :: codeFst a :: L2)
            (some true :: tail)⟩
      from copyCells_scan (2 * bitOf (codeFst a) + bitOf (codeSnd a)) hi
        (cs ++ [(a, false)])
        (by
          intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · exact hcs q hq
          · simp only [List.mem_singleton] at hq
            rw [hq])
        b1 b2 (some false :: codeSnd a :: codeFst a :: L2) tail]
  rfl


/-! ### 整块转写（源格序列归纳的材料） -/

/-- 源块编码：每格 `[codeFst, codeSnd, 标记 = true]`（源格标记为 `true`，表示待消费）。
    Source-block encoding with `true` (unread) markers. -/
def srcCells (cs : List Sym) : List Sym :=
  cs.flatMap (fun a => [codeFst a, codeSnd a, some true])

/-- 源块编码的首格展开。 Head expansion of the source-block encoding. -/
@[simp] theorem srcCells_cons (a : Sym) (rest : List Sym) :
    srcCells (a :: rest) = codeFst a :: codeSnd a :: some true :: srcCells rest := by
  simp [srcCells]

/-- 区域两端各补一格后的逆序展开（供末轮目标改写）。
    Inserting one mirror cell at both ends, unfolded in reverse order. -/
theorem codeCells_double (a : Sym) (q : List (Sym × Bool)) :
    (codeCells ([(a, false)] ++ q ++ [(a, false)])).reverse
      = [some false, codeSnd a, codeFst a] ++ (codeCells q).reverse ++
          [some false, codeSnd a, codeFst a] := by
  rw [codeCells_append, codeCells_append, List.reverse_append, List.reverse_append,
    codeCells_pair_false]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append,
    List.cons_append]

/-- 非空、标记全 `false` 的区域，其逆序串以标记 `some false` 开头。
    A non-empty all-`false` region starts, in reverse, with a `false` marker. -/
theorem codeCells_reverse_head :
    ∀ (q : List (Sym × Bool)), (∀ p ∈ q, p.2 = false) → q ≠ [] →
      ∃ E', (codeCells q).reverse = some false :: E'
  | [], _, hne => absurd rfl hne
  | [(a, m)], hq, _ => by
      have hm : m = false := hq (a, m) (by simp)
      subst hm
      exact ⟨[codeSnd a, codeFst a], by rw [codeCells_pair_false]; rfl⟩
  | (a, m) :: p2 :: ps, hq, _ => by
      have hsub : ∀ p ∈ p2 :: ps, p.2 = false :=
        fun p hp => hq p (List.mem_cons_of_mem _ hp)
      obtain ⟨E', hE'⟩ := codeCells_reverse_head (p2 :: ps) hsub (by simp)
      have hm : m = false := hq (a, m) (by simp)
      subst hm
      refine ⟨E' ++ [some false, codeSnd a, codeFst a], ?_⟩
      rw [codeCells_cons, cellCode_of_false (a, false) rfl, List.reverse_append, hE']
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]


/-- **末轮转写（区内为空）**：单格源块的完整转写。读 3 + 停 1 + 写 3 + 回 2 + 末轮流 4 = 13 步，
    停在 `99` 接受，左带为「两个镜像格」的逆序。
    Last round with an empty region: the single-cell block, 13 steps, halts accepting. -/
theorem copyCells_roundLastNil (a : Sym) (L2 tail : List Sym) :
    copyCells.run 13
      ⟨(⟨10, by omega⟩ : Fin 128),
        Tape.mk (codeSnd a :: codeFst a :: none :: none :: none :: L2)
          (some true :: none :: tail)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk ((codeCells ([(a, false)] ++ [(a, false)])).reverse ++ L2) (none :: tail)⟩ := by
  have hi : 2 * bitOf (codeFst a) + bitOf (codeSnd a) < 4 := by
    have h1 := bitOf_le_one (codeFst a)
    have h2 := bitOf_le_one (codeSnd a)
    omega
  -- 分段：读 3 + 停 1 + 写 3 + 回 2 + 末轮流 (3·1+1)
  rw [show (13 : Nat) = 3 + (1 + (3 + (2 + (3 * [(a, false)].length + 1)))) from by simp]
  rw [DTM.run_add copyCells 3 (1 + (3 + (2 + (3 * [(a, false)].length + 1))))]
  rw [show copyCells.run 3
        ⟨(⟨10, by omega⟩ : Fin 128),
          Tape.mk (codeSnd a :: codeFst a :: none :: none :: none :: L2)
            (some true :: none :: tail)⟩
      = ⟨(⟨20 + 2 * bitOf (codeFst a) + bitOf (codeSnd a), by omega⟩ : Fin 128),
          Tape.mk (none :: none :: L2)
            (none :: codeFst a :: codeSnd a :: some false :: none :: tail)⟩
      from copyCells_read3 a none (none :: none :: L2) (none :: tail)]
  rw [show (⟨20 + 2 * bitOf (codeFst a) + bitOf (codeSnd a), by omega⟩ : Fin 128)
        = (⟨20 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128)
      from Fin.ext (Nat.add_assoc 20 (2 * bitOf (codeFst a)) (bitOf (codeSnd a)))]
  rw [DTM.run_add copyCells 1 (3 + (2 + (3 * [(a, false)].length + 1)))]
  rw [show copyCells.run 1
        ⟨(⟨20 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (none :: none :: L2)
            (none :: codeFst a :: codeSnd a :: some false :: none :: tail)⟩
      = ⟨(⟨30 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (none :: none :: L2)
            (none :: codeFst a :: codeSnd a :: some false :: none :: tail)⟩
      from copyCells_walkStop (2 * bitOf (codeFst a) + bitOf (codeSnd a)) hi
        (none :: none :: L2)
        (codeFst a :: codeSnd a :: some false :: none :: tail)]
  rw [DTM.run_add copyCells 3 (2 + (3 * [(a, false)].length + 1))]
  rw [show copyCells.run 3
        ⟨(⟨30 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (none :: none :: L2)
            (none :: codeFst a :: codeSnd a :: some false :: none :: tail)⟩
      = ⟨(⟨42 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (codeFst a :: L2)
            (codeSnd a :: some false :: codeFst a :: codeSnd a :: some false :: none :: tail)⟩
      from copyCells_write3 a (2 * bitOf (codeFst a) + bitOf (codeSnd a)) hi rfl L2
        (codeFst a :: codeSnd a :: some false :: none :: tail)]
  rw [DTM.run_add copyCells 2 (3 * [(a, false)].length + 1)]
  rw [show copyCells.run 2
        ⟨(⟨42 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (codeFst a :: L2)
            (codeSnd a :: some false :: codeFst a :: codeSnd a :: some false :: none :: tail)⟩
      = ⟨(⟨50 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (some false :: codeSnd a :: codeFst a :: L2)
            (codeFst a :: codeSnd a :: some false :: none :: tail)⟩
      from copyCells_back2' (2 * bitOf (codeFst a) + bitOf (codeSnd a)) hi (codeSnd a) (some false)
        (codeFst a :: L2) (codeFst a :: codeSnd a :: some false :: none :: tail)]
  -- 新镜像格的编码并入末轮流匹配形态
  rw [show codeFst a :: codeSnd a :: some false :: none :: tail
        = codeCells [(a, false)] ++ none :: tail from by
    rw [codeCells_pair_false]; rfl]
  rw [show copyCells.run (3 * [(a, false)].length + 1)
        ⟨(⟨50 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (some false :: codeSnd a :: codeFst a :: L2)
            (codeCells [(a, false)] ++ none :: tail)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk ((codeCells [(a, false)]).reverse ++
              some false :: codeSnd a :: codeFst a :: L2) (none :: tail)⟩
      from copyCells_scanEnd (2 * bitOf (codeFst a) + bitOf (codeSnd a)) hi [(a, false)]
        (by intro p hp; simp only [List.mem_singleton] at hp; rw [hp])
        (some false :: codeSnd a :: codeFst a :: L2) tail]
  -- 目标形态：两端各一格的区域逆序
  rw [show (codeCells [(a, false)]).reverse ++ some false :: codeSnd a :: codeFst a :: L2
        = (codeCells ([(a, false)] ++ [(a, false)])).reverse ++ L2 from by
    rw [codeCells_append, codeCells_pair_false, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.append_assoc]]


/-- **末轮转写（区内非空）**：区域逆序串写作 `E = some false :: E'`。读 3 步、跨过 `E'`
    （`|E'| + 2` 步）、左向写镜像格 3 步、回右 2 步、末轮流 `3(|q|+1) + 1` 步，停在 `99`。
    Last round over a non-empty region `E = some false :: E'`, halting into `99`. -/
theorem copyCells_roundLast (a : Sym) (q : List (Sym × Bool)) (hq : ∀ p ∈ q, p.2 = false)
    (E E' : List Sym) (hE : E = (codeCells q).reverse) (hE' : E = some false :: E')
    (L2 tail : List Sym) :
    copyCells.run (3 + (E'.length + 2) + 3 + 2 + (3 * (q.length + 1) + 1))
      ⟨(⟨10, by omega⟩ : Fin 128),
        Tape.mk (codeSnd a :: codeFst a :: (E ++ none :: none :: none :: L2))
          (some true :: none :: tail)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk ((codeCells ([(a, false)] ++ q ++ [(a, false)])).reverse ++ L2)
            (none :: tail)⟩ := by
  -- 走左段前提：`E'` 的符号都是编码符号（非空白）
  have hl : ∀ y ∈ E', y ≠ none := by
    intro y hy
    have hyE : y ∈ E := by rw [hE']; exact List.mem_cons_of_mem _ hy
    rw [hE] at hyE
    exact codeCells_ne_none q y (List.mem_reverse.mp hyE)
  -- 状态码 `i = 2·b1' + b2'`
  have hi : 2 * bitOf (codeFst a) + bitOf (codeSnd a) < 4 := by
    have h1 := bitOf_le_one (codeFst a)
    have h2 := bitOf_le_one (codeSnd a)
    omega
  -- 分段：读 3 + 走 (|E'|+2) + 写 3 + 回 2 + 末轮流 (3(|q|+1)+1)
  rw [show 3 + (E'.length + 2) + 3 + 2 + (3 * (q.length + 1) + 1)
        = 3 + ((E'.length + 2) + (3 + (2 + (3 * (q.length + 1) + 1)))) from by omega]
  rw [hE']
  simp only [List.cons_append]
  rw [DTM.run_add copyCells 3 ((E'.length + 2) + (3 + (2 + (3 * (q.length + 1) + 1))))]
  rw [show copyCells.run 3
        ⟨(⟨10, by omega⟩ : Fin 128),
          Tape.mk (codeSnd a :: codeFst a :: some false ::
              (E' ++ none :: none :: none :: L2))
            (some true :: none :: tail)⟩
      = ⟨(⟨20 + 2 * bitOf (codeFst a) + bitOf (codeSnd a), by omega⟩ : Fin 128),
          Tape.mk (E' ++ none :: none :: none :: L2)
            (some false :: codeFst a :: codeSnd a :: some false :: none :: tail)⟩
      from copyCells_read3 a (some false) (E' ++ none :: none :: none :: L2) (none :: tail)]
  rw [show (⟨20 + 2 * bitOf (codeFst a) + bitOf (codeSnd a), by omega⟩ : Fin 128)
        = (⟨20 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128)
      from Fin.ext (Nat.add_assoc 20 (2 * bitOf (codeFst a)) (bitOf (codeSnd a)))]
  rw [DTM.run_add copyCells (E'.length + 2) (3 + (2 + (3 * (q.length + 1) + 1)))]
  rw [show copyCells.run (E'.length + 2)
        ⟨(⟨20 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (E' ++ none :: none :: none :: L2)
            (some false :: codeFst a :: codeSnd a :: some false :: none :: tail)⟩
      = ⟨(⟨30 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (none :: none :: L2)
            (none :: E'.reverse ++ some false :: codeFst a :: codeSnd a :: some false ::
              none :: tail)⟩
      from copyCells_walkL (2 * bitOf (codeFst a) + bitOf (codeSnd a)) hi E' hl false
        (none :: none :: L2)
        (codeFst a :: codeSnd a :: some false :: none :: tail)]
  rw [DTM.run_add copyCells 3 (2 + (3 * (q.length + 1) + 1))]
  rw [show copyCells.run 3
        ⟨(⟨30 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (none :: none :: L2)
            (none :: E'.reverse ++ some false :: codeFst a :: codeSnd a :: some false ::
              none :: tail)⟩
      = ⟨(⟨42 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (codeFst a :: L2)
            (codeSnd a :: some false :: E'.reverse ++ some false :: codeFst a :: codeSnd a ::
              some false :: none :: tail)⟩
      from copyCells_write3 a (2 * bitOf (codeFst a) + bitOf (codeSnd a)) hi rfl L2
        (E'.reverse ++ some false :: codeFst a :: codeSnd a :: some false :: none :: tail)]
  rw [DTM.run_add copyCells 2 (3 * (q.length + 1) + 1)]
  rw [show copyCells.run 2
        ⟨(⟨42 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (codeFst a :: L2)
            (codeSnd a :: some false :: E'.reverse ++ some false :: codeFst a :: codeSnd a ::
              some false :: none :: tail)⟩
      = ⟨(⟨50 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (some false :: codeSnd a :: codeFst a :: L2)
            (E'.reverse ++ some false :: codeFst a :: codeSnd a :: some false ::
              none :: tail)⟩
      from copyCells_back2' (2 * bitOf (codeFst a) + bitOf (codeSnd a)) hi (codeSnd a) (some false)
        (codeFst a :: L2)
        (E'.reverse ++ some false :: codeFst a :: codeSnd a :: some false :: none :: tail)]
  -- 区域逆序串还原成区域编码，再并上新格编码（供末轮流匹配）
  rw [show E'.reverse ++ some false :: codeFst a :: codeSnd a :: some false :: none :: tail
        = codeCells (q ++ [(a, false)]) ++ none :: tail from by
    rw [rev_cons_append E E' hE' (codeFst a :: codeSnd a :: some false :: none :: tail)]
    rw [hE, List.reverse_reverse]
    exact (codeCells_snoc_false q a (none :: tail)).symm]
  rw [show 3 * (q.length + 1) + 1 = 3 * (q ++ [(a, false)]).length + 1 from by simp]
  rw [show copyCells.run (3 * (q ++ [(a, false)]).length + 1)
        ⟨(⟨50 + (2 * bitOf (codeFst a) + bitOf (codeSnd a)), by omega⟩ : Fin 128),
          Tape.mk (some false :: codeSnd a :: codeFst a :: L2)
            (codeCells (q ++ [(a, false)]) ++ none :: tail)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk ((codeCells (q ++ [(a, false)])).reverse ++
              some false :: codeSnd a :: codeFst a :: L2) (none :: tail)⟩
      from copyCells_scanEnd (2 * bitOf (codeFst a) + bitOf (codeSnd a)) hi (q ++ [(a, false)])
        (by
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · exact hq p hp
          · simp only [List.mem_singleton] at hp
            rw [hp])
        (some false :: codeSnd a :: codeFst a :: L2) tail]
  rw [show (codeCells (q ++ [(a, false)])).reverse ++ some false :: codeSnd a :: codeFst a :: L2
        = (codeCells ([(a, false)] ++ q ++ [(a, false)])).reverse ++ L2 from by
    rw [codeCells_append, codeCells_append, codeCells_pair_false, List.reverse_append,
      List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append]
    rw [codeCells_cons, cellCode_of_false (a, false) rfl, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.singleton_append, List.append_assoc]]
  rfl


/-- 整块转写的预算成本：`m` = 当前区域格数，`r` = 剩余源格数（含当前格）。
    闭式 `6·m·r + 6r² + 9r − 2`；单轮递推为 `6m+15 + copyCost (m+2) r`。
    Budgeted block cost: `m` region cells, `r` remaining source cells. -/
def copyCost (m r : Nat) : Nat := 6 * (m * r) + 6 * (r * r) + 9 * r - 2

/-- 末轮（`r = 1`）成本：`6m + 13`。 -/
theorem copyCost_last (m : Nat) : copyCost m 1 = 6 * m + 13 := by
  unfold copyCost
  simp only [Nat.mul_one, Nat.one_mul]
  omega

/-- 单轮递推：区域长大两格、剩余源格少一，成本减 `6m+15`。
    One round of the block recursion. -/
theorem copyCost_step (m r : Nat) (hr : 1 ≤ r) :
    copyCost m (r + 1) = 6 * m + 15 + copyCost (m + 2) r := by
  unfold copyCost
  simp only [Nat.mul_succ, Nat.succ_mul, Nat.mul_add, Nat.add_assoc]
  omega



/-- 中间轮的区域逆序衔接：`reverse(codeCells (q ++ [c])) ++ [f, cS, cF] = reverse(codeCells ([c] ++ q ++ [c]))`。
    Bridging the mid-round region form to the paired-growth form. -/
theorem codeCells_mid_rev (a : Sym) (q : List (Sym × Bool)) :
    (codeCells (q ++ [(a, false)])).reverse ++ [some false, codeSnd a, codeFst a]
      = (codeCells ([(a, false)] ++ q ++ [(a, false)])).reverse := by
  rw [codeCells_double]
  rw [codeCells_append, codeCells_pair_false, List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.singleton_append, List.append_assoc]


/-- `n + 3` 个符号的重复串展开（空白垫改写用）。 -/
theorem replicate_three (n : Nat) (x : Sym) :
    List.replicate (n + 3) x = x :: x :: x :: List.replicate n x := by
  rw [show n + 3 = (n + 2) + 1 from rfl, List.replicate_succ,
    show n + 2 = (n + 1) + 1 from rfl, List.replicate_succ, List.replicate_succ]

/-- 首轮后的区域逆序衔接：单格区域 → 两格成对区域。 -/
theorem codeCells_first_rev_tail (a : Sym) (Y : List Sym) :
    (codeCells [(a, false)]).reverse ++ some false :: codeSnd a :: codeFst a :: Y
      = (codeCells ([(a, false)] ++ [(a, false)])).reverse ++ Y := by
  rw [codeCells_append, codeCells_pair_false, List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.singleton_append, List.append_assoc]

/-- 中间轮后的区域逆序衔接：`q ++ [c]` → 成对生长形态。 -/
theorem codeCells_mid_rev_tail (a : Sym) (q : List (Sym × Bool)) (Y : List Sym) :
    (codeCells (q ++ [(a, false)])).reverse ++ some false :: codeSnd a :: codeFst a :: Y
      = (codeCells ([(a, false)] ++ q ++ [(a, false)])).reverse ++ Y := by
  rw [codeCells_double, codeCells_append, codeCells_pair_false, List.reverse_append]
  simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
    List.singleton_append, List.append_assoc]


/-- 首轮（下一格以符号形式给出）：`15` 步，停在下一格标记位上。 -/
theorem copyCells_roundFirst' (a a2 : Sym) (tail L2 : List Sym) :
    copyCells.run 15
      ⟨(⟨10, by omega⟩ : Fin 128),
        Tape.mk (codeSnd a :: codeFst a :: none :: none :: none :: L2)
          (some true :: codeFst a2 :: codeSnd a2 :: some true :: tail)⟩
      = ⟨(⟨10, by omega⟩ : Fin 128),
          Tape.mk (codeSnd a2 :: codeFst a2 :: (codeCells [(a, false)]).reverse ++
              some false :: codeSnd a :: codeFst a :: L2) (some true :: tail)⟩ := by
  cases a2 with
  | none =>
      simpa only [codeFst, codeSnd, symCode, List.headD_cons, List.drop_zero,
        List.drop_succ_cons] using copyCells_roundFirst a false false tail L2
  | some b => cases b with
    | false =>
        simpa only [codeFst, codeSnd, symCode, List.headD_cons, List.drop_zero,
          List.drop_succ_cons] using copyCells_roundFirst a false true tail L2
    | true =>
        simpa only [codeFst, codeSnd, symCode, List.headD_cons, List.drop_zero,
          List.drop_succ_cons] using copyCells_roundFirst a true true tail L2

/-- 后续轮（下一格以符号形式给出）：区内非空，成本同 `copyCells_round`。 -/
theorem copyCells_round' (a a2 : Sym) (cs : List (Sym × Bool))
    (hcs : ∀ p ∈ cs, p.2 = false) (E E' : List Sym) (hE : E = (codeCells cs).reverse)
    (hE' : E = some false :: E') (tail L2 : List Sym) :
    copyCells.run (3 + (E'.length + 2) + 3 + 2 + (3 * (cs.length + 1) + 3))
      ⟨(⟨10, by omega⟩ : Fin 128),
        Tape.mk (codeSnd a :: codeFst a :: (E ++ none :: none :: none :: L2))
          (some true :: codeFst a2 :: codeSnd a2 :: some true :: tail)⟩
      = ⟨(⟨10, by omega⟩ : Fin 128),
          Tape.mk (codeSnd a2 :: codeFst a2 :: (codeCells (cs ++ [(a, false)])).reverse ++
              some false :: codeSnd a :: codeFst a :: L2) (some true :: tail)⟩ := by
  cases a2 with
  | none =>
      simpa only [codeFst, codeSnd, symCode, List.headD_cons, List.drop_zero,
        List.drop_succ_cons] using copyCells_round a cs hcs E E' hE hE' false false tail L2
  | some b => cases b with
    | false =>
        simpa only [codeFst, codeSnd, symCode, List.headD_cons, List.drop_zero,
          List.drop_succ_cons] using copyCells_round a cs hcs E E' hE hE' false true tail L2
    | true =>
        simpa only [codeFst, codeSnd, symCode, List.headD_cons, List.drop_zero,
          List.drop_succ_cons] using copyCells_round a cs hcs E E' hE hE' true true tail L2


/-- 末轮单圈（任意区域 `q`）：成本 `6|q| + 13`，停在 `99`。 -/
theorem copyCells_roundLastAll (a : Sym) (q : List (Sym × Bool)) (hq : ∀ p ∈ q, p.2 = false)
    (L2 tail : List Sym) :
    copyCells.run (6 * q.length + 13)
      ⟨(⟨10, by omega⟩ : Fin 128),
        Tape.mk (codeSnd a :: codeFst a ::
            ((codeCells q).reverse ++ none :: none :: none :: L2))
          (some true :: none :: tail)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk ((codeCells ([(a, false)] ++ q ++ [(a, false)])).reverse ++ L2)
            (none :: tail)⟩ := by
  cases q with
  | nil =>
      simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add, List.append_nil, List.nil_append,
        List.reverse_nil, List.cons_append, codeCells_append, List.append_assoc] using
        copyCells_roundLastNil a L2 tail
  | cons c ps =>
      obtain ⟨E', hE'⟩ := codeCells_reverse_head (c :: ps) hq (by simp)
      have hlen : E'.length + 1 = 3 * (c :: ps).length := by
        have hlen' := congrArg List.length hE'
        rw [List.length_reverse, codeCells_length] at hlen'
        simpa only [List.length_cons] using hlen'.symm
      have hcost : 6 * (c :: ps).length + 13
          = 3 + (E'.length + 2) + 3 + 2 + (3 * ((c :: ps).length + 1) + 1) := by
        omega
      rw [hcost]
      exact copyCells_roundLast a (c :: ps) hq ((codeCells (c :: ps)).reverse) E' rfl hE' L2 tail

set_option maxHeartbeats 1000000 in
/-- **整块转写**：从最左源格标记位起，把 `a :: rest` 全部消费并停下接受。区域逐轮
    `q' = [(a,false)] ++ q ++ [(a,false)]` 成对生长，成本 `copyCost |q| (|rest|+1)`。
    Whole-block transcription; the region grows one cell at both ends per round. -/
theorem copyCells_run (a : Sym) :
    ∀ (rest : List Sym) (q : List (Sym × Bool)), (∀ p ∈ q, p.2 = false) →
      ∀ (L2 tail : List Sym),
      copyCells.run (copyCost q.length (rest.length + 1))
        ⟨(⟨10, by omega⟩ : Fin 128),
          Tape.mk (codeSnd a :: codeFst a :: ((codeCells q).reverse ++
              List.replicate (3 * (rest.length + 1)) none ++ L2))
            (some true :: srcCells rest ++ none :: tail)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk ((codeCells ((List.map (fun x => (x, false)) rest).reverse ++
                [(a, false)] ++ q ++ [(a, false)] ++
              List.map (fun x => (x, false)) rest)).reverse ++ L2) (none :: tail)⟩
  | [], q, hq, L2, tail => by
      -- 剩一格：一次末轮单圈（r = 1，成本 6|q|+13）
      rw [show copyCost q.length (([].length) + 1) = 6 * q.length + 13 from by
        simpa using copyCost_last q.length]
      rw [show List.replicate (3 * (([].length) + 1)) none = [none, none, none] from by simp]
      simpa only [List.length_nil, Nat.zero_add, List.map_nil, List.reverse_nil,
        List.nil_append, List.cons_append, codeCells, List.flatMap_nil, List.append_assoc]
        using copyCells_roundLastAll a q hq L2 tail
  | a2 :: rest', q, hq, L2, tail => by
      -- 成本递推：一次非末轮（6|q|+15）+ 剩余（少一格、区域多两格）
      have hcost : copyCost q.length ((a2 :: rest').length + 1)
          = (6 * q.length + 15) + copyCost (q.length + 2) (rest'.length + 1) := by
        simp only [List.length_cons]
        exact copyCost_step q.length (rest'.length + 1) (by omega)
      rw [hcost]
      -- 空白垫：3r 个 = 3 + 3(r-1) 个
      rw [show List.replicate (3 * ((a2 :: rest').length + 1)) none
            = none :: none :: none :: List.replicate (3 * (rest'.length + 1)) none from by
          simp only [List.length_cons]
          rw [show rest'.length + 1 + 1 = (rest'.length + 1) + 1 from rfl, Nat.mul_succ,
            replicate_three]]
      -- 源块右带首格展开
      rw [show some true :: srcCells (a2 :: rest') ++ none :: tail
            = some true :: codeFst a2 :: codeSnd a2 :: some true ::
                (srcCells rest' ++ none :: tail) from by
          rw [srcCells_cons]; simp only [List.cons_append]]
      cases q with
      | nil =>
          -- 首轮：copyCells_roundFirst'（15 步）
          rw [show (6 * ([] : List (Sym × Bool)).length + 15) = 15 from by simp]
          rw [DTM.run_add copyCells 15 (copyCost (0 + 2) (rest'.length + 1))]
          rw [show copyCells.run 15
                ⟨(⟨10, by omega⟩ : Fin 128),
                  Tape.mk (codeSnd a :: codeFst a :: none :: none :: none ::
                      List.replicate (3 * (rest'.length + 1)) none ++ L2)
                    (some true :: codeFst a2 :: codeSnd a2 :: some true ::
                      (srcCells rest' ++ none :: tail))⟩
              = ⟨(⟨10, by omega⟩ : Fin 128),
                  Tape.mk (codeSnd a2 :: codeFst a2 :: (codeCells [(a, false)]).reverse ++
                      some false :: codeSnd a :: codeFst a ::
                      (List.replicate (3 * (rest'.length + 1)) none ++ L2))
                    (some true :: (srcCells rest' ++ none :: tail))⟩
              from copyCells_roundFirst' a a2 (srcCells rest' ++ none :: tail)
                (List.replicate (3 * (rest'.length + 1)) none ++ L2)]
          rw [codeCells_first_rev_tail a (List.replicate (3 * (rest'.length + 1)) none ++ L2)]
          simpa only [List.map_cons, List.reverse_cons, List.reverse_append,
            List.singleton_append, List.map_nil, List.reverse_nil, List.nil_append,
            List.cons_append, List.append_assoc, List.length_append, List.length_cons,
            List.length_nil, Nat.zero_add, Nat.add_zero]
            using copyCells_run a2 rest' ([(a, false)] ++ [(a, false)])
              (by intro p hp
                  simp only [List.mem_append, List.mem_singleton] at hp
                  rcases hp with hp | hp <;> rw [hp]) L2 tail
      | cons c ps =>
          -- 后续轮：copyCells_round'（6|q|+15 步）
          obtain ⟨E', hE'⟩ := codeCells_reverse_head (c :: ps) hq (by simp)
          have hlen : E'.length + 1 = 3 * (c :: ps).length := by
            have hlen' := congrArg List.length hE'
            rw [codeCells_length, List.length_reverse] at hlen'
            simp only [List.length_cons] at hlen'
            omega
          have hcost' : 6 * (c :: ps).length + 15
              = 3 + (E'.length + 2) + 3 + 2 + (3 * ((c :: ps).length + 1) + 3) := by
            omega
          rw [hcost']
          rw [DTM.run_add copyCells (3 + (E'.length + 2) + 3 + 2 + (3 * ((c :: ps).length + 1) + 3))
            (copyCost ((c :: ps).length + 2) (rest'.length + 1))]
          rw [show copyCells.run (3 + (E'.length + 2) + 3 + 2 + (3 * ((c :: ps).length + 1) + 3))
                ⟨(⟨10, by omega⟩ : Fin 128),
                  Tape.mk (codeSnd a :: codeFst a ::
                      ((codeCells (c :: ps)).reverse ++ none :: none :: none ::
                        List.replicate (3 * (rest'.length + 1)) none ++ L2))
                    (some true :: codeFst a2 :: codeSnd a2 :: some true ::
                      (srcCells rest' ++ none :: tail))⟩
              = ⟨(⟨10, by omega⟩ : Fin 128),
                  Tape.mk (codeSnd a2 :: codeFst a2 ::
                      (codeCells ((c :: ps) ++ [(a, false)])).reverse ++
                      some false :: codeSnd a :: codeFst a ::
                      (List.replicate (3 * (rest'.length + 1)) none ++ L2))
                    (some true :: (srcCells rest' ++ none :: tail))⟩
              from copyCells_round' a a2 (c :: ps) hq ((codeCells (c :: ps)).reverse) E' rfl hE'
                (srcCells rest' ++ none :: tail)
                (List.replicate (3 * (rest'.length + 1)) none ++ L2)]
          rw [codeCells_mid_rev_tail a (c :: ps) (List.replicate (3 * (rest'.length + 1)) none ++ L2)]
          simpa only [List.map_cons, List.reverse_cons, List.reverse_append,
            List.singleton_append, List.map_nil, List.reverse_nil, List.nil_append,
            List.cons_append, List.append_assoc, List.length_append, List.length_cons,
            List.length_nil, Nat.zero_add, Nat.add_zero]
            using copyCells_run a2 rest' ([(a, false)] ++ (c :: ps) ++ [(a, false)])
              (by intro p hp
                  simp only [List.mem_append, List.mem_singleton] at hp
                  rcases hp with hp | hp <;> rw [hp]) L2 tail



end DTM

end Pnp
