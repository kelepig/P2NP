/-
  文件：Pnp/Machine/ExpandRun.lean
  File: Pnp/Machine/ExpandRun.lean

  主题：展开机 `expand` 的运行分析（逐步逼近整段运行 `expand_run`）。
  Topic: run analysis of the expansion machine `expand`, building up to `expand_run`.

  证明套路（#151 教训）：所有步进写成「字面量状态 + 字面量读符号」，
  `estep1` 给出一步、`etape` 把纸带项归一到 `Tape.mk` 形态，再 `rfl` 收口。
  Proof recipe: every step is taken at a literal state and literal read symbol;
  `estep1` gives one step, `etape` normalises the tape term to `Tape.mk` form.
-/

import Pnp.Machine.Expand

namespace Pnp

namespace DTM

/-- **单步运行**：给定显式转移（在字面量状态与读符号上由 `rfl` 给出），
    `run 1` 即「写入 + 移动」后的格局。
    One explicit step: under a literal state and read symbol, `run 1` is write-and-move. -/
theorem estep1 (st : Nat) (hst : st < 128) (a : Sym) (q' : Fin 128) (s : Sym) (d : Dir)
    (h : expand.step ⟨st, hst⟩ a = (q', s, d)) (M : List Sym) (R : List Sym) (hne : st ≠ 99) :
    expand.run 1 ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩
      = ⟨q', (Tape.mk M (a :: R)).write s |>.move d⟩ := by
  rw [show (1 : Nat) = 0 + 1 from rfl]
  rw [DTM.run_succ_of_not_halted _ 0 _ (expand_halted_ne st hst hne _)]
  exact stepConfig_of_step expand ⟨⟨st, hst⟩, Tape.mk M (a :: R)⟩ q' s d h

/-- 把「写入 + 移动」的纸带项归一到 `Tape.mk` 显式形态，便于下一步匹配。
    Normalise the write/move tape term to explicit `Tape.mk` form. -/
macro "etape" : tactic => `(tactic|
  (dsimp only [Tape.write, Tape.move, Tape.moveLeft, Tape.moveRight, List.tail_cons,
     List.headD_cons, List.headD_nil, List.cons_append, List.append_assoc, List.nil_append]))

/-! ### 入口状态 0 -/

/-- 入口读到空白：接受。 -/
theorem expand_entry_none (M R : List Sym) :
    expand.run 1 ⟨(⟨0, by omega⟩ : Fin 128), Tape.mk M (none :: R)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128), Tape.mk M (none :: R)⟩ := by
  rw [estep1 0 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  rfl

/-- 入口读到 `some false`：进入循环状态 10，并右移到下一格。 -/
theorem expand_entry_false (M R : List Sym) :
    expand.run 1 ⟨(⟨0, by omega⟩ : Fin 128), Tape.mk M (some false :: R)⟩
      = ⟨(⟨10, by omega⟩ : Fin 128), Tape.mk (some false :: M) R⟩ := by
  rw [estep1 0 (by omega) (some false) _ _ _ (by rfl) _ _ (by omega)]
  rfl

/-- 入口读到 `some true`：进入循环状态 11，并右移到下一格。 -/
theorem expand_entry_true (M R : List Sym) :
    expand.run 1 ⟨(⟨0, by omega⟩ : Fin 128), Tape.mk M (some true :: R)⟩
      = ⟨(⟨11, by omega⟩ : Fin 128), Tape.mk (some true :: M) R⟩ := by
  rw [estep1 0 (by omega) (some true) _ _ _ (by rfl) _ _ (by omega)]
  rfl

/-! ### 末符号路径（后缀为空时的直接写下） -/

/-- 状态 60 的转移与读符号无关（写 `codeFst` 并右移）。 -/
theorem expand_step_60 (a : Sym) :
    expand.step (⟨60, by omega⟩ : Fin 128) a
      = ((⟨62, by omega⟩ : Fin 128), codeFst (some false), Dir.right) := by
  cases a <;> rfl

/-- 状态 61 的转移与读符号无关（写 `codeFst` 并右移）。 -/
theorem expand_step_61 (a : Sym) :
    expand.step (⟨61, by omega⟩ : Fin 128) a
      = ((⟨63, by omega⟩ : Fin 128), codeFst (some true), Dir.right) := by
  cases a <;> rfl

/-- 后缀为空（情形 1）：4 步写出 `codeSnd`、`codeFst`、标记，回到状态 0。 -/
theorem expand_last_false (v : Sym) (L R : List Sym) :
    expand.run (1 + (1 + (1 + 1)))
      ⟨(⟨10, by omega⟩ : Fin 128), Tape.mk (v :: L) (none :: none :: none :: R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 128),
          Tape.mk (some false :: codeSnd (some false) :: codeFst (some false) :: L)
            (none :: R)⟩ := by
  rw [DTM.run_add expand 1 (1 + (1 + 1))]
  rw [estep1 10 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [DTM.run_add expand 1 (1 + 1)]
  rw [estep1 60 (by omega) v _ _ _ (expand_step_60 v) _ _ (by omega)]
  etape
  rw [DTM.run_add expand 1 1]
  rw [estep1 62 (by omega) (codeSnd (some false)) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [estep1 64 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape

/-- 后缀为空（情形 2）：4 步写出 `codeSnd`、`codeFst`、标记，回到状态 0。 -/
theorem expand_last_true (v : Sym) (L R : List Sym) :
    expand.run (1 + (1 + (1 + 1)))
      ⟨(⟨11, by omega⟩ : Fin 128), Tape.mk (v :: L) (none :: none :: none :: R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 128),
          Tape.mk (some false :: codeSnd (some true) :: codeFst (some true) :: L)
            (none :: R)⟩ := by
  rw [DTM.run_add expand 1 (1 + (1 + 1))]
  rw [estep1 11 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [DTM.run_add expand 1 (1 + 1)]
  rw [estep1 61 (by omega) v _ _ _ (expand_step_61 v) _ _ (by omega)]
  etape
  rw [DTM.run_add expand 1 1]
  rw [estep1 63 (by omega) (codeSnd (some true)) _ _ _ (by rfl) _ _ (by omega)]
  etape
  rw [estep1 65 (by omega) none _ _ _ (by rfl) _ _ (by omega)]
  etape


/-! ### 后继所需的字面量枚举小工具 -/

/-- Nat 三情形（`< 3`）显式枚举，替代 Mathlib 的 `interval_cases`。 -/
theorem nat_lt3_cases {n : Nat} (h : n < 3) : n = 0 ∨ n = 1 ∨ n = 2 := by omega

/-- Nat 两情形（`< 2`）显式枚举。 -/
theorem nat_lt2_cases {n : Nat} (h : n < 2) : n = 0 ∨ n = 1 := by omega

/-- 回扫段（情形 1）：读到非空白，原样写回并左移。 -/
theorem expand_step_50_walk (a : Sym) (ha : a ≠ none) :
    expand.step (⟨50, by omega⟩ : Fin 128) a = ((⟨50, by omega⟩ : Fin 128), a, Dir.left) := by
  cases a with
  | none => exact absurd rfl ha
  | some b => cases b <;> rfl

/-- 回扫段（情形 1）：读到空白，落标记并左移。 -/
theorem expand_step_50_mark :
    expand.step (⟨50, by omega⟩ : Fin 128) none
      = ((⟨52, by omega⟩ : Fin 128), some false, Dir.left) := rfl

/-- 回扫段（情形 1）：写 `codeSnd` 并左移（与读符号无关）。 -/
theorem expand_step_52 (a : Sym) :
    expand.step (⟨52, by omega⟩ : Fin 128) a
      = ((⟨54, by omega⟩ : Fin 128), codeSnd (some false), Dir.left) := by cases a <;> rfl

/-- 回扫段（情形 1）：写 `codeFst` 并右移（与读符号无关）。 -/
theorem expand_step_54 (a : Sym) :
    expand.step (⟨54, by omega⟩ : Fin 128) a
      = ((⟨56, by omega⟩ : Fin 128), codeFst (some false), Dir.right) := by cases a <;> rfl

/-- 回扫段（情形 1）：原样写回并右移。 -/
theorem expand_step_56 (a : Sym) :
    expand.step (⟨56, by omega⟩ : Fin 128) a = ((⟨58, by omega⟩ : Fin 128), a, Dir.right) := by
  cases a <;> rfl

/-- 回扫段（情形 1）：最后一步原样写回并右移，回到入口状态 0。 -/
theorem expand_step_58 (a : Sym) :
    expand.step (⟨58, by omega⟩ : Fin 128) a = ((⟨0, by omega⟩ : Fin 128), a, Dir.right) := by
  cases a <;> rfl
/-- 回扫段（情形 2）：读到非空白，原样写回并左移。 -/
theorem expand_step_51_walk (a : Sym) (ha : a ≠ none) :
    expand.step (⟨51, by omega⟩ : Fin 128) a = ((⟨51, by omega⟩ : Fin 128), a, Dir.left) := by
  cases a with
  | none => exact absurd rfl ha
  | some b => cases b <;> rfl

/-- 回扫段（情形 2）：读到空白，落标记并左移。 -/
theorem expand_step_51_mark :
    expand.step (⟨51, by omega⟩ : Fin 128) none
      = ((⟨53, by omega⟩ : Fin 128), some false, Dir.left) := rfl

/-- 回扫段（情形 2）：写 `codeSnd` 并左移（与读符号无关）。 -/
theorem expand_step_53 (a : Sym) :
    expand.step (⟨53, by omega⟩ : Fin 128) a
      = ((⟨55, by omega⟩ : Fin 128), codeSnd (some true), Dir.left) := by cases a <;> rfl

/-- 回扫段（情形 2）：写 `codeFst` 并右移（与读符号无关）。 -/
theorem expand_step_55 (a : Sym) :
    expand.step (⟨55, by omega⟩ : Fin 128) a
      = ((⟨57, by omega⟩ : Fin 128), codeFst (some true), Dir.right) := by cases a <;> rfl

/-- 回扫段（情形 2）：原样写回并右移。 -/
theorem expand_step_57 (a : Sym) :
    expand.step (⟨57, by omega⟩ : Fin 128) a = ((⟨59, by omega⟩ : Fin 128), a, Dir.right) := by
  cases a <;> rfl

/-- 回扫段（情形 2）：最后一步原样写回并右移，回到入口状态 0。 -/
theorem expand_step_59 (a : Sym) :
    expand.step (⟨59, by omega⟩ : Fin 128) a = ((⟨0, by omega⟩ : Fin 128), a, Dir.right) := by
  cases a <;> rfl

/-! ### 回扫与落码（按情形展开） -/

/-- **回扫收尾（情形 1）**：从 `50` 起向左掠过整段非空白串（原样写回），
    在空白处落标记、写 `codeSnd`/`codeFst`，回到入口状态 0。
    Walk-back (case 1): skips the shifted block leftwards and writes the cell code. -/
theorem expand_finish_false (bs : List Sym) :
    ∀ (hbs : ∀ x ∈ bs, x ≠ none) (b : Sym) (hb : b ≠ none) (a : Sym) (M T : List Sym),
      expand.run (bs.length + 6)
        ⟨(⟨50, by omega⟩ : Fin 128), Tape.mk (bs ++ none :: none :: a :: M) (b :: T)⟩
        = ⟨(⟨0, by omega⟩ : Fin 128),
            Tape.mk (some false :: codeSnd (some false) :: codeFst (some false) :: M)
              (List.reverse bs ++ b :: T)⟩ := by
  induction bs with
  | nil =>
    intro hbs b hb a M T
    rw [show ([].length + 6) = 1 + (1 + (1 + (1 + (1 + 1)))) from rfl]
    simp only [List.nil_append]
    cases b with
    | none => exact absurd rfl hb
    | some bb =>
      cases bb with
      | false =>
        rw [DTM.run_add expand 1 (1 + (1 + (1 + (1 + 1))))]
        rw [estep1 50 (by omega) (some false) _ _ _ (expand_step_50_walk (some false) (by simp)) _ _ (by omega)]
        etape
        rw [DTM.run_add expand 1 (1 + (1 + (1 + 1)))]
        rw [estep1 50 (by omega) none _ _ _ (expand_step_50_mark) _ _ (by omega)]
        etape
        rw [DTM.run_add expand 1 (1 + (1 + 1))]
        rw [estep1 52 (by omega) none _ _ _ (expand_step_52 none) _ _ (by omega)]
        etape
        rw [DTM.run_add expand 1 (1 + 1)]
        rw [estep1 54 (by omega) a _ _ _ (expand_step_54 a) _ _ (by omega)]
        etape
        rw [DTM.run_add expand 1 1]
        rw [estep1 56 (by omega) (codeSnd (some false)) _ _ _ (expand_step_56 _) _ _ (by omega)]
        etape
        rw [estep1 58 (by omega) (some false) _ _ _ (expand_step_58 _) _ _ (by omega)]
        etape
        simp
      | true =>
        rw [DTM.run_add expand 1 (1 + (1 + (1 + (1 + 1))))]
        rw [estep1 50 (by omega) (some true) _ _ _ (expand_step_50_walk (some true) (by simp)) _ _ (by omega)]
        etape
        rw [DTM.run_add expand 1 (1 + (1 + (1 + 1)))]
        rw [estep1 50 (by omega) none _ _ _ (expand_step_50_mark) _ _ (by omega)]
        etape
        rw [DTM.run_add expand 1 (1 + (1 + 1))]
        rw [estep1 52 (by omega) none _ _ _ (expand_step_52 none) _ _ (by omega)]
        etape
        rw [DTM.run_add expand 1 (1 + 1)]
        rw [estep1 54 (by omega) a _ _ _ (expand_step_54 a) _ _ (by omega)]
        etape
        rw [DTM.run_add expand 1 1]
        rw [estep1 56 (by omega) (codeSnd (some false)) _ _ _ (expand_step_56 _) _ _ (by omega)]
        etape
        rw [estep1 58 (by omega) (some false) _ _ _ (expand_step_58 _) _ _ (by omega)]
        etape
        simp
  | cons s ss ih =>
    intro hbs b hb a M T
    rw [show (s :: ss).length + 6 = 1 + (ss.length + 6) from by simp only [List.length_cons]; omega]
    rw [DTM.run_add expand 1 (ss.length + 6)]
    cases b with
    | none => exact absurd rfl hb
    | some bb =>
      cases bb with
      | false =>
        rw [estep1 50 (by omega) (some false) _ _ _ (expand_step_50_walk (some false) (by simp)) _ _ (by omega)]
        etape
        rw [ih (fun x hx => hbs x (List.mem_cons_of_mem _ hx)) s (hbs s (by simp)) a M (some false :: T)]
        simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
      | true =>
        rw [estep1 50 (by omega) (some true) _ _ _ (expand_step_50_walk (some true) (by simp)) _ _ (by omega)]
        etape
        rw [ih (fun x hx => hbs x (List.mem_cons_of_mem _ hx)) s (hbs s (by simp)) a M (some true :: T)]
        simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

/-- **回扫收尾（情形 2）**：从 `51` 起向左掠过整段非空白串（原样写回），
    在空白处落标记、写 `codeSnd`/`codeFst`，回到入口状态 0。
    Walk-back (case 2): skips the shifted block leftwards and writes the cell code. -/
theorem expand_finish_true (bs : List Sym) :
    ∀ (hbs : ∀ x ∈ bs, x ≠ none) (b : Sym) (hb : b ≠ none) (a : Sym) (M T : List Sym),
      expand.run (bs.length + 6)
        ⟨(⟨51, by omega⟩ : Fin 128), Tape.mk (bs ++ none :: none :: a :: M) (b :: T)⟩
        = ⟨(⟨0, by omega⟩ : Fin 128),
            Tape.mk (some false :: codeSnd (some true) :: codeFst (some true) :: M)
              (List.reverse bs ++ b :: T)⟩ := by
  induction bs with
  | nil =>
    intro hbs b hb a M T
    rw [show ([].length + 6) = 1 + (1 + (1 + (1 + (1 + 1)))) from rfl]
    simp only [List.nil_append]
    cases b with
    | none => exact absurd rfl hb
    | some bb =>
      cases bb with
      | false =>
        rw [DTM.run_add expand 1 (1 + (1 + (1 + (1 + 1))))]
        rw [estep1 51 (by omega) (some false) _ _ _ (expand_step_51_walk (some false) (by simp)) _ _ (by omega)]
        etape
        rw [DTM.run_add expand 1 (1 + (1 + (1 + 1)))]
        rw [estep1 51 (by omega) none _ _ _ (expand_step_51_mark) _ _ (by omega)]
        etape
        rw [DTM.run_add expand 1 (1 + (1 + 1))]
        rw [estep1 53 (by omega) none _ _ _ (expand_step_53 none) _ _ (by omega)]
        etape
        rw [DTM.run_add expand 1 (1 + 1)]
        rw [estep1 55 (by omega) a _ _ _ (expand_step_55 a) _ _ (by omega)]
        etape
        rw [DTM.run_add expand 1 1]
        rw [estep1 57 (by omega) (codeSnd (some true)) _ _ _ (expand_step_57 _) _ _ (by omega)]
        etape
        rw [estep1 59 (by omega) (some false) _ _ _ (expand_step_59 _) _ _ (by omega)]
        etape
        simp
      | true =>
        rw [DTM.run_add expand 1 (1 + (1 + (1 + (1 + 1))))]
        rw [estep1 51 (by omega) (some true) _ _ _ (expand_step_51_walk (some true) (by simp)) _ _ (by omega)]
        etape
        rw [DTM.run_add expand 1 (1 + (1 + (1 + 1)))]
        rw [estep1 51 (by omega) none _ _ _ (expand_step_51_mark) _ _ (by omega)]
        etape
        rw [DTM.run_add expand 1 (1 + (1 + 1))]
        rw [estep1 53 (by omega) none _ _ _ (expand_step_53 none) _ _ (by omega)]
        etape
        rw [DTM.run_add expand 1 (1 + 1)]
        rw [estep1 55 (by omega) a _ _ _ (expand_step_55 a) _ _ (by omega)]
        etape
        rw [DTM.run_add expand 1 1]
        rw [estep1 57 (by omega) (codeSnd (some true)) _ _ _ (expand_step_57 _) _ _ (by omega)]
        etape
        rw [estep1 59 (by omega) (some false) _ _ _ (expand_step_59 _) _ _ (by omega)]
        etape
        simp
  | cons s ss ih =>
    intro hbs b hb a M T
    rw [show (s :: ss).length + 6 = 1 + (ss.length + 6) from by simp only [List.length_cons]; omega]
    rw [DTM.run_add expand 1 (ss.length + 6)]
    cases b with
    | none => exact absurd rfl hb
    | some bb =>
      cases bb with
      | false =>
        rw [estep1 51 (by omega) (some false) _ _ _ (expand_step_51_walk (some false) (by simp)) _ _ (by omega)]
        etape
        rw [ih (fun x hx => hbs x (List.mem_cons_of_mem _ hx)) s (hbs s (by simp)) a M (some false :: T)]
        simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]
      | true =>
        rw [estep1 51 (by omega) (some true) _ _ _ (expand_step_51_walk (some true) (by simp)) _ _ (by omega)]
        etape
        rw [ih (fun x hx => hbs x (List.mem_cons_of_mem _ hx)) s (hbs s (by simp)) a M (some true :: T)]
        simp only [List.reverse_cons, List.append_assoc, List.cons_append, List.nil_append]

/-! ### 循环体：转移引理与整段运行 -/

/-- **循环体移位一步**：两个携带符号与读符号不全为空白时，把 `x` 写回当前格、
    右移一格，携带翻转为 `(y, a)`。
    One shifting step: unless all of `x`, `y`, `a` are blank, write back `x`,
    move right, and shift the carry pair to `(y, a)`. -/
theorem body_step (x y a : Sym) (ci : Nat) (hci : ci < 2)
    (h : x ≠ none ∨ y ≠ none ∨ a ≠ none) (M R : List Sym) :
    expand.run 1
      ⟨(⟨qLoop (symCase x) (symCase y) 1 ci,
          by have h1 := symCase_le x; have h2 := symCase_le y; unfold qLoop; omega⟩ : Fin 128),
        Tape.mk M (a :: R)⟩
      = ⟨(⟨qLoop (symCase y) (symCase a) 1 ci,
            by have h1 := symCase_le y; have h2 := symCase_le a; unfold qLoop; omega⟩ : Fin 128),
          Tape.mk (caseSym (symCase x) :: M) R⟩ := by
  rcases nat_lt2_cases hci with hc | hc
  · subst hc
    cases x with
    | none =>
      cases y with
      | none =>
        cases a with
        | none =>
          cases h with
          | inl h1 => exact absurd rfl h1
          | inr h1 => cases h1 with
            | inl h2 => exact absurd rfl h2
            | inr h3 => exact absurd rfl h3
        | some ba =>
          cases ba with
          | false =>
            dsimp only [symCase]
            rw [estep1 (qLoop 0 0 1 0) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
            etape
            rfl
          | true =>
            dsimp only [symCase]
            rw [estep1 (qLoop 0 0 1 0) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
            etape
            rfl
      | some byy =>
        cases byy with
        | false =>
          cases a with
          | none =>
            dsimp only [symCase]
            rw [estep1 (qLoop 0 1 1 0) (by simp only [qLoop]; omega) (none) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
            etape
            rfl
          | some ba =>
            cases ba with
            | false =>
              dsimp only [symCase]
              rw [estep1 (qLoop 0 1 1 0) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
            | true =>
              dsimp only [symCase]
              rw [estep1 (qLoop 0 1 1 0) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
        | true =>
          cases a with
          | none =>
            dsimp only [symCase]
            rw [estep1 (qLoop 0 2 1 0) (by simp only [qLoop]; omega) (none) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
            etape
            rfl
          | some ba =>
            cases ba with
            | false =>
              dsimp only [symCase]
              rw [estep1 (qLoop 0 2 1 0) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
            | true =>
              dsimp only [symCase]
              rw [estep1 (qLoop 0 2 1 0) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
    | some bx =>
      cases bx with
      | false =>
        cases y with
        | none =>
          cases a with
          | none =>
            dsimp only [symCase]
            rw [estep1 (qLoop 1 0 1 0) (by simp only [qLoop]; omega) (none) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
            etape
            rfl
          | some ba =>
            cases ba with
            | false =>
              dsimp only [symCase]
              rw [estep1 (qLoop 1 0 1 0) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
            | true =>
              dsimp only [symCase]
              rw [estep1 (qLoop 1 0 1 0) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
        | some byy =>
          cases byy with
          | false =>
            cases a with
            | none =>
              dsimp only [symCase]
              rw [estep1 (qLoop 1 1 1 0) (by simp only [qLoop]; omega) (none) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
            | some ba =>
              cases ba with
              | false =>
                dsimp only [symCase]
                rw [estep1 (qLoop 1 1 1 0) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
                etape
                rfl
              | true =>
                dsimp only [symCase]
                rw [estep1 (qLoop 1 1 1 0) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
                etape
                rfl
          | true =>
            cases a with
            | none =>
              dsimp only [symCase]
              rw [estep1 (qLoop 1 2 1 0) (by simp only [qLoop]; omega) (none) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
            | some ba =>
              cases ba with
              | false =>
                dsimp only [symCase]
                rw [estep1 (qLoop 1 2 1 0) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
                etape
                rfl
              | true =>
                dsimp only [symCase]
                rw [estep1 (qLoop 1 2 1 0) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
                etape
                rfl
      | true =>
        cases y with
        | none =>
          cases a with
          | none =>
            dsimp only [symCase]
            rw [estep1 (qLoop 2 0 1 0) (by simp only [qLoop]; omega) (none) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
            etape
            rfl
          | some ba =>
            cases ba with
            | false =>
              dsimp only [symCase]
              rw [estep1 (qLoop 2 0 1 0) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
            | true =>
              dsimp only [symCase]
              rw [estep1 (qLoop 2 0 1 0) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
        | some byy =>
          cases byy with
          | false =>
            cases a with
            | none =>
              dsimp only [symCase]
              rw [estep1 (qLoop 2 1 1 0) (by simp only [qLoop]; omega) (none) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
            | some ba =>
              cases ba with
              | false =>
                dsimp only [symCase]
                rw [estep1 (qLoop 2 1 1 0) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
                etape
                rfl
              | true =>
                dsimp only [symCase]
                rw [estep1 (qLoop 2 1 1 0) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
                etape
                rfl
          | true =>
            cases a with
            | none =>
              dsimp only [symCase]
              rw [estep1 (qLoop 2 2 1 0) (by simp only [qLoop]; omega) (none) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
            | some ba =>
              cases ba with
              | false =>
                dsimp only [symCase]
                rw [estep1 (qLoop 2 2 1 0) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
                etape
                rfl
              | true =>
                dsimp only [symCase]
                rw [estep1 (qLoop 2 2 1 0) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
                etape
                rfl
  · subst hc
    cases x with
    | none =>
      cases y with
      | none =>
        cases a with
        | none =>
          cases h with
          | inl h1 => exact absurd rfl h1
          | inr h1 => cases h1 with
            | inl h2 => exact absurd rfl h2
            | inr h3 => exact absurd rfl h3
        | some ba =>
          cases ba with
          | false =>
            dsimp only [symCase]
            rw [estep1 (qLoop 0 0 1 1) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
            etape
            rfl
          | true =>
            dsimp only [symCase]
            rw [estep1 (qLoop 0 0 1 1) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
            etape
            rfl
      | some byy =>
        cases byy with
        | false =>
          cases a with
          | none =>
            dsimp only [symCase]
            rw [estep1 (qLoop 0 1 1 1) (by simp only [qLoop]; omega) (none) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
            etape
            rfl
          | some ba =>
            cases ba with
            | false =>
              dsimp only [symCase]
              rw [estep1 (qLoop 0 1 1 1) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
            | true =>
              dsimp only [symCase]
              rw [estep1 (qLoop 0 1 1 1) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
        | true =>
          cases a with
          | none =>
            dsimp only [symCase]
            rw [estep1 (qLoop 0 2 1 1) (by simp only [qLoop]; omega) (none) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
            etape
            rfl
          | some ba =>
            cases ba with
            | false =>
              dsimp only [symCase]
              rw [estep1 (qLoop 0 2 1 1) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
            | true =>
              dsimp only [symCase]
              rw [estep1 (qLoop 0 2 1 1) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
    | some bx =>
      cases bx with
      | false =>
        cases y with
        | none =>
          cases a with
          | none =>
            dsimp only [symCase]
            rw [estep1 (qLoop 1 0 1 1) (by simp only [qLoop]; omega) (none) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
            etape
            rfl
          | some ba =>
            cases ba with
            | false =>
              dsimp only [symCase]
              rw [estep1 (qLoop 1 0 1 1) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
            | true =>
              dsimp only [symCase]
              rw [estep1 (qLoop 1 0 1 1) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
        | some byy =>
          cases byy with
          | false =>
            cases a with
            | none =>
              dsimp only [symCase]
              rw [estep1 (qLoop 1 1 1 1) (by simp only [qLoop]; omega) (none) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
            | some ba =>
              cases ba with
              | false =>
                dsimp only [symCase]
                rw [estep1 (qLoop 1 1 1 1) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
                etape
                rfl
              | true =>
                dsimp only [symCase]
                rw [estep1 (qLoop 1 1 1 1) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
                etape
                rfl
          | true =>
            cases a with
            | none =>
              dsimp only [symCase]
              rw [estep1 (qLoop 1 2 1 1) (by simp only [qLoop]; omega) (none) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
            | some ba =>
              cases ba with
              | false =>
                dsimp only [symCase]
                rw [estep1 (qLoop 1 2 1 1) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
                etape
                rfl
              | true =>
                dsimp only [symCase]
                rw [estep1 (qLoop 1 2 1 1) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
                etape
                rfl
      | true =>
        cases y with
        | none =>
          cases a with
          | none =>
            dsimp only [symCase]
            rw [estep1 (qLoop 2 0 1 1) (by simp only [qLoop]; omega) (none) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
            etape
            rfl
          | some ba =>
            cases ba with
            | false =>
              dsimp only [symCase]
              rw [estep1 (qLoop 2 0 1 1) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
            | true =>
              dsimp only [symCase]
              rw [estep1 (qLoop 2 0 1 1) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
        | some byy =>
          cases byy with
          | false =>
            cases a with
            | none =>
              dsimp only [symCase]
              rw [estep1 (qLoop 2 1 1 1) (by simp only [qLoop]; omega) (none) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
            | some ba =>
              cases ba with
              | false =>
                dsimp only [symCase]
                rw [estep1 (qLoop 2 1 1 1) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
                etape
                rfl
              | true =>
                dsimp only [symCase]
                rw [estep1 (qLoop 2 1 1 1) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
                etape
                rfl
          | true =>
            cases a with
            | none =>
              dsimp only [symCase]
              rw [estep1 (qLoop 2 2 1 1) (by simp only [qLoop]; omega) (none) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
              etape
              rfl
            | some ba =>
              cases ba with
              | false =>
                dsimp only [symCase]
                rw [estep1 (qLoop 2 2 1 1) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
                etape
                rfl
              | true =>
                dsimp only [symCase]
                rw [estep1 (qLoop 2 2 1 1) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
                etape
                rfl
/-- **循环体停止一步**：两个携带符号都是空白且读到空白时，写回空白、左移，
    进入回扫段 `50+ci`。
    Stopping step: with both carries and the read cell blank, write blank, move left,
    and enter the walk-back segment `50+ci`. -/
theorem body_step_stop (ci : Nat) (hci : ci < 2) (Lh : Sym) (M R : List Sym) :
    expand.run 1
      ⟨(⟨qLoop 0 0 1 ci, by simp only [qLoop]; omega⟩ : Fin 128),
        Tape.mk (Lh :: M) (none :: R)⟩
      = ⟨(⟨50 + ci, by omega⟩ : Fin 128), Tape.mk M (Lh :: none :: R)⟩ := by
  rcases nat_lt2_cases hci with hc | hc
  · subst hc
    rw [estep1 (qLoop 0 0 1 0) (by simp only [qLoop]; omega) none _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
    etape
  · subst hc
    rw [estep1 (qLoop 0 0 1 1) (by simp only [qLoop]; omega) none _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
    etape
/-- **循环体整段运行**：从携带 `(x, y)` 出发，走过串 `bs` 与非空白标记 `b`，
    `|bs|+4` 步后把 `x`、`y`、`bs` 逆序写回左侧，停在回扫段 `50+ci`。
    Whole body run: starting with carries `(x, y)`, walk across `bs` and the non-blank
    marker `b`; after `|bs|+4` steps the reversed carry/block list is on the left. -/
theorem expand_body (bs : List Sym) :
    ∀ (hbs : ∀ v ∈ bs, v ≠ none) (b : Sym) (hb : b ≠ none)
      (x y : Sym) (ci : Nat) (hci : ci < 2) (M R : List Sym),
      expand.run (bs.length + 4)
        ⟨(⟨qLoop (symCase x) (symCase y) 1 ci,
            by have h1 := symCase_le x; have h2 := symCase_le y; unfold qLoop; omega⟩ : Fin 128),
          Tape.mk M (bs ++ b :: none :: none :: none :: R)⟩
        = ⟨(⟨50 + ci, by omega⟩ : Fin 128),
            Tape.mk (List.reverse (x :: y :: bs) ++ M) (b :: none :: R)⟩ := by
  induction bs with
  | nil =>
    intro hbs b hb x y ci hci M R
    rw [show ([].length + 4) = 1 + (1 + (1 + 1)) from rfl]
    simp only [List.nil_append]
    rw [DTM.run_add expand 1 (1 + (1 + 1))]
    rw [body_step x y b ci hci (Or.inr (Or.inr hb)) M (none :: none :: none :: R)]
    try etape
    rw [DTM.run_add expand 1 (1 + 1)]
    rw [body_step y b none ci hci (Or.inr (Or.inl hb)) (caseSym (symCase x) :: M) (none :: none :: R)]
    try etape
    rw [DTM.run_add expand 1 1]
    rw [body_step b none none ci hci (Or.inl hb)
      (caseSym (symCase y) :: caseSym (symCase x) :: M) (none :: R)]
    try etape
    dsimp only [symCase]
    rw [body_step_stop ci hci (caseSym (symCase b))
      (caseSym (symCase y) :: caseSym (symCase x) :: M) R]
    try etape
    simp only [caseSym_symCase, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.append_assoc, List.cons_append]
  | cons a bs ih =>
    intro hbs b hb x y ci hci M R
    rw [show (a :: bs).length + 4 = 1 + (bs.length + 4) from by simp only [List.length_cons]; omega]
    rw [DTM.run_add expand 1 (bs.length + 4)]
    cases a with
    | none => exact absurd rfl (hbs none (by simp))
    | some aa =>
      simp only [List.cons_append]
      rw [body_step x y (some aa) ci hci (Or.inr (Or.inr (by simp))) M
        (bs ++ b :: none :: none :: none :: R)]
      try etape
      rw [ih (fun v hv => hbs v (List.mem_cons_of_mem _ hv)) b hb y (some aa) ci hci
        (caseSym (symCase x) :: M) R]
      simp only [caseSym_symCase, List.reverse_cons, List.nil_append,
        List.append_assoc, List.cons_append]

/-- **展开机：启动步**：两个携带符号为空、尚未启动时读到非空白 `b`，
    把空白写回当前格并右移，携带翻转为 `(none, b)`、进入启动态 `s = 1`。
    Start step: with blank carries and `s = 0`, reading `b ≠ blank` writes blank and
    advances, flipping the carry pair to `(none, b)` and setting `s = 1`. -/
theorem expand_start (b : Sym) (hb : b ≠ none) (ci : Nat) (hci : ci < 2) (M R : List Sym) :
    expand.run 1
      ⟨(⟨qLoop 0 0 0 ci, by simp only [qLoop]; omega⟩ : Fin 128),
        Tape.mk M (b :: R)⟩
      = ⟨(⟨qLoop 0 (symCase b) 1 ci,
            by have h := symCase_le b; unfold qLoop; omega⟩ : Fin 128),
          Tape.mk (none :: M) R⟩ := by
  rcases nat_lt2_cases hci with hc | hc
  · subst hc
    cases b with
    | none => exact absurd rfl hb
    | some bb => cases bb with
      | false =>
        dsimp only [symCase]
        rw [estep1 (qLoop 0 0 0 0) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
        etape
        try rfl
      | true =>
        dsimp only [symCase]
        rw [estep1 (qLoop 0 0 0 0) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
        etape
        try rfl
  · subst hc
    cases b with
    | none => exact absurd rfl hb
    | some bb => cases bb with
      | false =>
        dsimp only [symCase]
        rw [estep1 (qLoop 0 0 0 1) (by simp only [qLoop]; omega) (some false) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
        etape
        try rfl
      | true =>
        dsimp only [symCase]
        rw [estep1 (qLoop 0 0 0 1) (by simp only [qLoop]; omega) (some true) _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
        etape
        try rfl

/-- **展开机：双符号块的冲刷段**：携带 `(none, b)` 且读到连续三格空白时，
    三步把空白与 `b` 写到左侧空白格，停在回扫段 `50+ci`。
    Flush of the two-symbol block: with carry pair `(none, b)` and three blanks ahead,
    write blank and `b` leftwards in three steps and stop in the walk-back segment. -/
theorem expand_flush (b : Sym) (hb : b ≠ none) (ci : Nat) (hci : ci < 2) (M R : List Sym) :
    expand.run 3
      ⟨(⟨qLoop 0 (symCase b) 1 ci,
          by have h := symCase_le b; unfold qLoop; omega⟩ : Fin 128),
        Tape.mk M (none :: none :: none :: R)⟩
      = ⟨(⟨50 + ci, by omega⟩ : Fin 128), Tape.mk (none :: M) (b :: none :: R)⟩ := by
  rcases nat_lt2_cases hci with hc | hc
  · subst hc
    cases b with
    | none => exact absurd rfl hb
    | some bb => cases bb with
      | false =>
        rw [show (3 : Nat) = 1 + (1 + 1) from rfl]
        rw [DTM.run_add expand 1 (1 + 1)]
        dsimp only [symCase]
        rw [estep1 (qLoop 0 1 1 0) (by simp only [qLoop]; omega) none _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
        etape
        rw [DTM.run_add expand 1 1]
        rw [estep1 (qLoop 1 0 1 0) (by simp only [qLoop]; omega) none _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
        etape
        rw [estep1 (qLoop 0 0 1 0) (by simp only [qLoop]; omega) none _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
        etape
        try rfl
      | true =>
        rw [show (3 : Nat) = 1 + (1 + 1) from rfl]
        rw [DTM.run_add expand 1 (1 + 1)]
        dsimp only [symCase]
        rw [estep1 (qLoop 0 2 1 0) (by simp only [qLoop]; omega) none _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
        etape
        rw [DTM.run_add expand 1 1]
        rw [estep1 (qLoop 2 0 1 0) (by simp only [qLoop]; omega) none _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
        etape
        rw [estep1 (qLoop 0 0 1 0) (by simp only [qLoop]; omega) none _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
        etape
        try rfl
  · subst hc
    cases b with
    | none => exact absurd rfl hb
    | some bb => cases bb with
      | false =>
        rw [show (3 : Nat) = 1 + (1 + 1) from rfl]
        rw [DTM.run_add expand 1 (1 + 1)]
        dsimp only [symCase]
        rw [estep1 (qLoop 0 1 1 1) (by simp only [qLoop]; omega) none _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
        etape
        rw [DTM.run_add expand 1 1]
        rw [estep1 (qLoop 1 0 1 1) (by simp only [qLoop]; omega) none _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
        etape
        rw [estep1 (qLoop 0 0 1 1) (by simp only [qLoop]; omega) none _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
        etape
        try rfl
      | true =>
        rw [show (3 : Nat) = 1 + (1 + 1) from rfl]
        rw [DTM.run_add expand 1 (1 + 1)]
        dsimp only [symCase]
        rw [estep1 (qLoop 0 2 1 1) (by simp only [qLoop]; omega) none _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
        etape
        rw [DTM.run_add expand 1 1]
        rw [estep1 (qLoop 2 0 1 1) (by simp only [qLoop]; omega) none _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
        etape
        rw [estep1 (qLoop 0 0 1 1) (by simp only [qLoop]; omega) none _ _ _ (by rfl) _ _ (by simp only [qLoop]; omega)]
        etape
        try rfl

/-- **展开机：双符号块的一轮**（`[a, b]`）：入口写 `a`、启动步吃进 `b`、冲刷段腾出两格，
    回扫段写下 `a` 的格编码。步数 11。
    Round on a two-symbol block `[a, b]`: entry, start, flush and walk-back in 11 steps. -/
theorem expand_round2 (a b : Sym) (ha : a ≠ none) (hb : b ≠ none) (M R : List Sym) :
    expand.run 11
      ⟨(⟨0, by omega⟩ : Fin 128),
        Tape.mk M (a :: b :: none :: none :: none :: none :: none :: R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 128),
          Tape.mk (some false :: codeSnd a :: codeFst a :: M)
            (b :: none :: none :: none :: R)⟩ := by
  cases a with
  | none => exact absurd rfl ha
  | some ca =>
    cases ca with
    | false =>
      try simp only [List.cons_append, List.append_assoc, List.nil_append]
      rw [show (11 : Nat) = 1 + (1 + (3 + 6)) from rfl]
      rw [DTM.run_add expand 1 (1 + (3 + 6))]
      rw [expand_entry_false M (b :: none :: none :: none :: none :: none :: R)]
      have h2 : expand.run 1
          ⟨(⟨10, by omega⟩ : Fin 128),
            Tape.mk (some false :: M) (b :: none :: none :: none :: none :: none :: R)⟩
          = ⟨(⟨qLoop 0 (symCase b) 1 0,
                by have h := symCase_le b; unfold qLoop; omega⟩ : Fin 128),
              Tape.mk (none :: some false :: M) (none :: none :: none :: none :: none :: R)⟩ :=
        expand_start b hb 0 (by omega) (some false :: M)
          (none :: none :: none :: none :: none :: R)
      rw [DTM.run_add expand 1 (3 + 6)]
      rw [h2]
      have h3 : expand.run 3
          ⟨(⟨qLoop 0 (symCase b) 1 0,
                by have h := symCase_le b; unfold qLoop; omega⟩ : Fin 128),
            Tape.mk (none :: some false :: M) (none :: none :: none :: none :: none :: R)⟩
          = ⟨(⟨50, by omega⟩ : Fin 128),
              Tape.mk (none :: none :: some false :: M) (b :: none :: none :: none :: R)⟩ :=
        expand_flush b hb 0 (by omega) (none :: some false :: M) (none :: none :: R)
      rw [DTM.run_add expand 3 6]
      rw [h3]
      have h4 : expand.run 6
          ⟨(⟨50, by omega⟩ : Fin 128),
            Tape.mk (none :: none :: some false :: M) (b :: none :: none :: none :: R)⟩
          = ⟨(⟨0, by omega⟩ : Fin 128),
              Tape.mk (some false :: codeSnd (some false) :: codeFst (some false) :: M)
                (b :: none :: none :: none :: R)⟩ :=
        expand_finish_false [] (by simp) b hb (some false) M (none :: none :: none :: R)
      rw [h4]
    | true =>
      try simp only [List.cons_append, List.append_assoc, List.nil_append]
      rw [show (11 : Nat) = 1 + (1 + (3 + 6)) from rfl]
      rw [DTM.run_add expand 1 (1 + (3 + 6))]
      rw [expand_entry_true M (b :: none :: none :: none :: none :: none :: R)]
      have h2 : expand.run 1
          ⟨(⟨11, by omega⟩ : Fin 128),
            Tape.mk (some true :: M) (b :: none :: none :: none :: none :: none :: R)⟩
          = ⟨(⟨qLoop 0 (symCase b) 1 1,
                by have h := symCase_le b; unfold qLoop; omega⟩ : Fin 128),
              Tape.mk (none :: some true :: M) (none :: none :: none :: none :: none :: R)⟩ :=
        expand_start b hb 1 (by omega) (some true :: M)
          (none :: none :: none :: none :: none :: R)
      rw [DTM.run_add expand 1 (3 + 6)]
      rw [h2]
      have h3 : expand.run 3
          ⟨(⟨qLoop 0 (symCase b) 1 1,
                by have h := symCase_le b; unfold qLoop; omega⟩ : Fin 128),
            Tape.mk (none :: some true :: M) (none :: none :: none :: none :: none :: R)⟩
          = ⟨(⟨51, by omega⟩ : Fin 128),
              Tape.mk (none :: none :: some true :: M) (b :: none :: none :: none :: R)⟩ :=
        expand_flush b hb 1 (by omega) (none :: some true :: M) (none :: none :: R)
      rw [DTM.run_add expand 3 6]
      rw [h3]
      have h4 : expand.run 6
          ⟨(⟨51, by omega⟩ : Fin 128),
            Tape.mk (none :: none :: some true :: M) (b :: none :: none :: none :: R)⟩
          = ⟨(⟨0, by omega⟩ : Fin 128),
              Tape.mk (some false :: codeSnd (some true) :: codeFst (some true) :: M)
                (b :: none :: none :: none :: R)⟩ :=
        expand_finish_true [] (by simp) b hb (some true) M (none :: none :: none :: R)
      rw [h4]

/-- **展开机：一般轮（块长 ≥ 3）**：入口写 `a`、启动步吃进 `b`、循环体把 `bs` 与末符号 `bl`
    右移两格，回扫段写下 `a` 的格编码。步数 `2|bs|+13`。
    General round for blocks of length ≥ 3 (entry, start, body, walk-back). -/
theorem expand_round (a b bl : Sym) (bs : List Sym) (ha : a ≠ none) (hb : b ≠ none)
    (hbs : ∀ v ∈ bs, v ≠ none) (hbl : bl ≠ none) (M R : List Sym) :
    expand.run (2 * bs.length + 13)
      ⟨(⟨0, by omega⟩ : Fin 128),
        Tape.mk M ((a :: b :: (bs ++ [bl])) ++ none :: none :: none :: R)⟩
      = ⟨(⟨0, by omega⟩ : Fin 128),
          Tape.mk (some false :: codeSnd a :: codeFst a :: M)
            ((b :: (bs ++ [bl])) ++ none :: R)⟩ := by
  cases a with
  | none => exact absurd rfl ha
  | some ca =>
    cases ca with
    | false =>
      try simp only [List.cons_append, List.append_assoc, List.nil_append]
      rw [show 2 * bs.length + 13 = 1 + (1 + ((bs.length + 4) + (bs.length + 7))) from by omega]
      rw [DTM.run_add expand 1 (1 + ((bs.length + 4) + (bs.length + 7)))]
      rw [expand_entry_false M (b :: (bs ++ bl :: none :: none :: none :: R))]
      have h2 : expand.run 1
          ⟨(⟨10, by omega⟩ : Fin 128),
            Tape.mk (some false :: M) (b :: (bs ++ bl :: none :: none :: none :: R))⟩
          = ⟨(⟨qLoop (symCase (none : Sym)) (symCase b) 1 0,
                by have h := symCase_le (none : Sym); have h2 := symCase_le b; unfold qLoop; omega⟩ : Fin 128),
              Tape.mk (none :: some false :: M) (bs ++ bl :: none :: none :: none :: R)⟩ :=
        expand_start b hb 0 (by omega) (some false :: M) (bs ++ bl :: none :: none :: none :: R)
      rw [DTM.run_add expand 1 ((bs.length + 4) + (bs.length + 7))]
      rw [h2]
      try simp only [List.cons_append, List.append_assoc, List.nil_append]
      rw [DTM.run_add expand (bs.length + 4) (bs.length + 7)]
      have hrev : ∀ v ∈ List.reverse bs ++ [b], v ≠ none := by
        intro v hv
        simp only [List.mem_append, List.mem_singleton, List.mem_reverse] at hv
        rcases hv with hv | rfl
        · exact hbs v hv
        · exact hb
      have h3 : expand.run (bs.length + 4)
          ⟨(⟨qLoop (symCase (none : Sym)) (symCase b) 1 0,
                by have h := symCase_le (none : Sym); have h2 := symCase_le b; unfold qLoop; omega⟩ : Fin 128),
            Tape.mk (none :: some false :: M) (bs ++ bl :: none :: none :: none :: R)⟩
          = ⟨(⟨50, by omega⟩ : Fin 128),
              Tape.mk (List.reverse bs ++ b :: none :: none :: some false :: M) (bl :: none :: R)⟩ := by
        simpa only [qLoop, symCase, caseSym_symCase, List.reverse_cons, List.nil_append,
          List.cons_append, List.append_assoc, Nat.zero_mul, Nat.mul_zero, Nat.one_mul,
          Nat.mul_one, Nat.add_zero, Nat.zero_add]
          using expand_body bs hbs bl hbl none b 0 (by omega) (none :: some false :: M) R
      rw [h3]
      try simp only [List.cons_append, List.append_assoc, List.nil_append]
      have hlen : bs.length + 7 = (List.reverse bs ++ [b]).length + 6 := by
        simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse]
        try omega
      have htape : (List.reverse bs ++ b :: none :: none :: some false :: M)
          = ((List.reverse bs ++ [b]) ++ none :: none :: some false :: M) := by
        simp only [List.cons_append, List.append_assoc, List.nil_append]
      rw [hlen, htape]
      rw [expand_finish_false (List.reverse bs ++ [b]) hrev bl hbl (some false) M (none :: R)]
      try simp only [List.reverse_append, List.reverse_reverse, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, List.append_assoc]
    | true =>
      try simp only [List.cons_append, List.append_assoc, List.nil_append]
      rw [show 2 * bs.length + 13 = 1 + (1 + ((bs.length + 4) + (bs.length + 7))) from by omega]
      rw [DTM.run_add expand 1 (1 + ((bs.length + 4) + (bs.length + 7)))]
      rw [expand_entry_true M (b :: (bs ++ bl :: none :: none :: none :: R))]
      have h2 : expand.run 1
          ⟨(⟨11, by omega⟩ : Fin 128),
            Tape.mk (some true :: M) (b :: (bs ++ bl :: none :: none :: none :: R))⟩
          = ⟨(⟨qLoop (symCase (none : Sym)) (symCase b) 1 1,
                by have h := symCase_le (none : Sym); have h2 := symCase_le b; unfold qLoop; omega⟩ : Fin 128),
              Tape.mk (none :: some true :: M) (bs ++ bl :: none :: none :: none :: R)⟩ :=
        expand_start b hb 1 (by omega) (some true :: M) (bs ++ bl :: none :: none :: none :: R)
      rw [DTM.run_add expand 1 ((bs.length + 4) + (bs.length + 7))]
      rw [h2]
      try simp only [List.cons_append, List.append_assoc, List.nil_append]
      rw [DTM.run_add expand (bs.length + 4) (bs.length + 7)]
      have hrev : ∀ v ∈ List.reverse bs ++ [b], v ≠ none := by
        intro v hv
        simp only [List.mem_append, List.mem_singleton, List.mem_reverse] at hv
        rcases hv with hv | rfl
        · exact hbs v hv
        · exact hb
      have h3 : expand.run (bs.length + 4)
          ⟨(⟨qLoop (symCase (none : Sym)) (symCase b) 1 1,
                by have h := symCase_le (none : Sym); have h2 := symCase_le b; unfold qLoop; omega⟩ : Fin 128),
            Tape.mk (none :: some true :: M) (bs ++ bl :: none :: none :: none :: R)⟩
          = ⟨(⟨51, by omega⟩ : Fin 128),
              Tape.mk (List.reverse bs ++ b :: none :: none :: some true :: M) (bl :: none :: R)⟩ := by
        simpa only [qLoop, symCase, caseSym_symCase, List.reverse_cons, List.nil_append,
          List.cons_append, List.append_assoc, Nat.zero_mul, Nat.mul_zero, Nat.one_mul,
          Nat.mul_one, Nat.add_zero, Nat.zero_add]
          using expand_body bs hbs bl hbl none b 1 (by omega) (none :: some true :: M) R
      rw [h3]
      try simp only [List.cons_append, List.append_assoc, List.nil_append]
      have hlen : bs.length + 7 = (List.reverse bs ++ [b]).length + 6 := by
        simp only [List.length_append, List.length_cons, List.length_nil, List.length_reverse]
        try omega
      have htape : (List.reverse bs ++ b :: none :: none :: some true :: M)
          = ((List.reverse bs ++ [b]) ++ none :: none :: some true :: M) := by
        simp only [List.cons_append, List.append_assoc, List.nil_append]
      rw [hlen, htape]
      rw [expand_finish_true (List.reverse bs ++ [b]) hrev bl hbl (some true) M (none :: R)]
      try simp only [List.reverse_append, List.reverse_reverse, List.reverse_cons, List.reverse_nil,
        List.nil_append, List.cons_append, List.append_assoc]

/-! ### 运行步数函数 -/

/-- 展开整段非空白串的步数（递归定义）。
    Step count for expanding a whole non-blank block (recursive). -/
def expandCost : List Sym → Nat
  | [] => 1
  | [_] => 6
  | _ :: b :: rest => 2 * (b :: rest).length + 9 + expandCost (b :: rest)

/-! ### 单符号块的完整运行 -/

/-- **单符号块的完整运行**：`[a]` 在 3 个空白之后，6 步内展开成
    `[codeFst a, codeSnd a, some false]` 并接受。
    Full run on a one-symbol block: expanded into one cell code in 6 steps. -/
theorem expand_run_sing (a : Sym) (ha : a ≠ none) (M R : List Sym) :
    expand.run (expandCost [a])
      ⟨(⟨0, by omega⟩ : Fin 128), Tape.mk M (a :: none :: none :: none :: R)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128),
          Tape.mk (some false :: codeSnd a :: codeFst a :: M) (none :: R)⟩ := by
  rw [show expandCost [a] = 1 + ((1 + (1 + (1 + 1))) + 1) from rfl]
  rw [DTM.run_add expand 1 ((1 + (1 + (1 + 1))) + 1)]
  cases a with
  | none => exact absurd rfl ha
  | some b =>
    cases b with
    | false =>
        rw [expand_entry_false]
        rw [DTM.run_add expand (1 + (1 + (1 + 1))) 1]
        rw [expand_last_false]
        rw [expand_entry_none]
    | true =>
        rw [expand_entry_true]
        rw [DTM.run_add expand (1 + (1 + (1 + 1))) 1]
        rw [expand_last_true]
        rw [expand_entry_none]

/-! ### 整段块的完整运行 -/

/-- 一个符号在左带上写下的三格编码：标记、`codeSnd`、`codeFst`。
    The three cells written on the left tape for one symbol. -/
def symCode3 (a : Sym) : List Sym := [some false, codeSnd a, codeFst a]

/-- 整段块展开后左带上的编码串（后处理的符号更靠左）。
    Codes of a whole block on the left tape (later symbols nearer the head). -/
def codesRev : List Sym → List Sym
  | [] => []
  | a :: rest => codesRev rest ++ symCode3 a

/-- 非空的符号表总能写成「某个前缀 ++ 末元素」。
    A non-empty list is a prefix followed by a one-element suffix. -/
theorem exists_append_singleton : ∀ (t : List Sym), t ≠ [] → ∃ bs bl, t = bs ++ [bl]
  | [], h => absurd rfl h
  | [_], _ => ⟨[], _, rfl⟩
  | x :: y :: t, _ => by
      obtain ⟨bs, bl, h⟩ := exists_append_singleton (y :: t) (by simp)
      exact ⟨x :: bs, bl, by rw [h]; try rfl⟩

/-- **整段块的完整运行**：从入口状态 0 出发，非空白块 `l` 后跟 `2|l|+1` 个空白，
    `expandCost l` 步内把整块展开成左带编码串 `codesRev l` 并接受（停在空白格）。
    Whole-block run: from the entry state, a non-blank block `l` followed by
    `2|l|+1` blanks is expanded into the code string `codesRev l` in `expandCost l`
    steps, then accepted with the head on a blank. -/
theorem expand_run (l : List Sym) (hl : ∀ v ∈ l, v ≠ none) (M R : List Sym) :
    expand.run (expandCost l)
      ⟨(⟨0, by omega⟩ : Fin 128),
        Tape.mk M (l ++ List.replicate (2 * l.length + 1) none ++ R)⟩
      = ⟨(⟨99, by omega⟩ : Fin 128), Tape.mk (codesRev l ++ M) (none :: R)⟩ := by
  revert M R hl
  induction l with
  | nil =>
      intro hl M R
      exact expand_entry_none M R
  | cons a t ih =>
      intro hl M R
      cases t with
      | nil => exact expand_run_sing a (hl a (by simp)) M R
      | cons b rest =>
          have ha : a ≠ none := hl a (by simp)
          have hb : b ≠ none := hl b (by simp)
          have hrest : ∀ v ∈ b :: rest, v ≠ none := by
            intro v hv
            exact hl v (List.mem_cons_of_mem a hv)
          rw [show expandCost (a :: b :: rest)
                = (2 * (b :: rest).length + 9) + expandCost (b :: rest) from rfl]
          rw [DTM.run_add expand (2 * (b :: rest).length + 9) (expandCost (b :: rest))]
          cases rest with
          | nil =>
              rw [show 2 * (b :: []).length + 9 = 11 from rfl]
              rw [show (a :: b :: []) ++ List.replicate (2 * (a :: b :: []).length + 1) none ++ R
                    = a :: b :: none :: none :: none :: none :: none :: R from rfl]
              rw [expand_round2 a b ha hb M R]
              rw [show b :: none :: none :: none :: R
                    = (b :: []) ++ List.replicate (2 * (b :: []).length + 1) none ++ R
                  from rfl]
              rw [show (some false :: codeSnd a :: codeFst a :: M) = (symCode3 a ++ M)
                    from rfl]
              rw [ih hrest (symCode3 a ++ M) R]
              simp only [codesRev, symCode3, List.append_assoc, List.nil_append]
          | cons c rest' =>
              obtain ⟨bs, bl, hbs⟩ := exists_append_singleton (c :: rest') (by simp)
              rw [hbs]
              rw [hbs] at ih
              have hrest' : ∀ v ∈ b :: (bs ++ [bl]), v ≠ none := by
                intro v hv
                exact hrest v (by rw [hbs]; exact hv)
              have hbs' : ∀ v ∈ bs, v ≠ none := by
                intro v hv
                exact hrest' v (List.mem_cons_of_mem b (List.mem_append.mpr (Or.inl hv)))
              have hbl : bl ≠ none := by
                exact hrest' bl (List.mem_cons_of_mem b
                  (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))))
              rw [show 2 * (b :: (bs ++ [bl])).length + 9 = 2 * bs.length + 13 from by
                simp only [List.length_cons, List.length_append, List.length_nil]
                omega]
              have htap : (a :: b :: (bs ++ [bl]))
                    ++ List.replicate (2 * (a :: b :: (bs ++ [bl])).length + 1) none ++ R
                  = (a :: b :: (bs ++ [bl])) ++ none :: none :: none
                      :: (List.replicate (2 * bs.length + 4) none ++ R) := by
                have hlen : (a :: b :: (bs ++ [bl])).length = (bs ++ [bl]).length + 2 := by
                  simp only [List.length_cons]
                  try omega
                rw [hlen]
                simp only [List.length_append, List.length_singleton, List.append_assoc]
                rfl
              rw [htap]
              rw [expand_round a b bl bs ha hb hbs' hbl M
                (List.replicate (2 * bs.length + 4) none ++ R)]
              have htap2 : (b :: (bs ++ [bl]))
                    ++ none :: (List.replicate (2 * bs.length + 4) none ++ R)
                  = (b :: (bs ++ [bl]))
                      ++ List.replicate (2 * (b :: (bs ++ [bl])).length + 1) none ++ R := by
                have hlen : (b :: (bs ++ [bl])).length = (bs ++ [bl]).length + 1 := by
                  simp only [List.length_cons]
                rw [hlen]
                simp only [List.length_append, List.length_singleton, List.append_assoc]
                rfl
              rw [htap2]
              rw [show (some false :: codeSnd a :: codeFst a :: M) = (symCode3 a ++ M)
                    from rfl]
              rw [ih hrest' (symCode3 a ++ M) R]
              simp only [codesRev, symCode3, List.append_assoc, List.nil_append]


/-! ### 与区域编码 `Reg.enc` 的桥接 -/

/-- `symCode3 a` 是格编码 `cellCode (a, false)` 的逆序（标记位为 0）。
    `symCode3 a` is the reverse of the cell code `cellCode (a, false)`. -/
theorem symCode3_reverse (a : Sym) :
    symCode3 a = List.reverse (cellCode (a, false)) := by
  simp only [symCode3, cellCode, symCode_eq, List.singleton_append, List.reverse_append,
    List.reverse_cons, List.reverse_nil, List.nil_append, Bool.false_eq_true, ite_false]

/-- 整段块写下的编码串 `codesRev l` = 格序列编码串的逆序。
    The code string written by `expand` is the reverse of the cell-code string. -/
theorem codesRev_eq_reverse_codeCells (l : List Sym) :
    codesRev l = List.reverse (codeCells (l.map (fun s => (s, false)))) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
      simp only [codesRev, codeCells, List.map_cons, List.flatMap_cons, List.reverse_append]
      rw [ih, symCode3_reverse]
      rfl


end DTM

end Pnp
