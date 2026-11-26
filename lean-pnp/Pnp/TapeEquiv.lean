/-
  文件：Pnp/TapeEquiv.lean
  主题：「空白填充等价」：两端多余空白不影响读写（B5 阶段 3c-ii 前置）。

  编码/解码会把空纸带规范化为一个空白格，左移还会产生额外空白。
  因此模拟正确性不能用结构相等，需要允许两端任意多个空白格。
  本文件先定义 `trimNone`（去掉尾部空白）与 `Tape.equiv`，
  再证明读写与左右移动都保持等价，最后推广到 `DTM.run`。
-/

import Pnp.TapeEncoding

namespace Pnp

namespace Tape

/-- 去掉列表末尾的所有空白符号。 -/
def trimNone : List Sym → List Sym
  | [] => []
  | s :: rest =>
      match trimNone rest with
      | [] => if s = none then [] else [s]
      | t => s :: t

/-- 末尾追加空白不改变 `trimNone`。 -/
theorem trimNone_append_none (l : List Sym) :
    trimNone (l ++ [none]) = trimNone l := by
  induction l with
  | nil => simp [trimNone]
  | cons s rest ih =>
      simp only [List.cons_append]
      unfold trimNone
      rw [ih]

/-- `trimNone l = []` 当且仅当 `l` 全是空白。 -/
theorem trimNone_eq_nil_iff {l : List Sym} :
    trimNone l = [] ↔ ∀ x : Sym, x ∈ l → x = none := by
  induction l with
  | nil => simp [trimNone]
  | cons s rest ih =>
      constructor
      · -- 结果为空 ⇒ 头和尾部都只能是空白
        intro h x hx
        rcases List.mem_cons.mp hx with heq | hx
        · -- x = s
          cases hrest : trimNone rest with
          | nil =>
              simp [trimNone, hrest] at h
              by_cases hs : s = none
              · rw [heq, hs]
              · simp [hs] at h
          | cons t ts =>
              simp [trimNone, hrest] at h
        · have hrest : trimNone rest = [] := by
            cases h' : trimNone rest with
            | nil => rfl
            | cons t ts => simp [trimNone, h'] at h
          exact ih.mp hrest x hx
      · -- 全是空白 ⇒ 结果为空
        intro hall
        have hs : s = none := hall s List.mem_cons_self
        have hr : ∀ x : Sym, x ∈ rest → x = none :=
          fun x hx => hall x (List.mem_cons_of_mem _ hx)
        have hrest : trimNone rest = [] := ih.mpr hr
        simp [trimNone, hrest, hs]

/-- 头部为空白时，整体 trim 为空等价于尾部 trim 为空。 -/
theorem trimNone_none_cons_eq_nil {rs : List Sym} :
    trimNone (none :: rs) = [] ↔ trimNone rs = [] := by
  change (match trimNone rs with
          | [] => if none = none then [] else [none]
          | t => none :: t) = [] ↔ trimNone rs = []
  cases trimNone rs <;> simp

/-- 头非空白时，`trimNone` 直接保留头。 -/
theorem trimNone_cons_of_ne {r : Sym} (hr : r ≠ none) (rs : List Sym) :
    trimNone (r :: rs) = r :: trimNone rs := by
  -- 只展开左边的一次
  change (match trimNone rs with
          | [] => if r = none then [] else [r]
          | t => r :: t) = r :: trimNone rs
  rw [ite_eq_right hr]
  cases trimNone rs with
  | nil => rfl
  | cons a as => rfl

/-- 若 `r :: rs` 与 `r :: rs'` 的 `trimNone` 相同，则尾部也相同。 -/
theorem trimNone_cons_inj (r : Sym) {rs rs' : List Sym}
    (h : trimNone (r :: rs) = trimNone (r :: rs')) :
    trimNone rs = trimNone rs' := by
  by_cases hr : r = none
  · subst hr
    cases h1 : trimNone rs with
    | nil =>
        cases h2 : trimNone rs' with
        | nil => rfl
        | cons t ts =>
            simp [trimNone, h1, h2] at h
    | cons t ts =>
        cases h2 : trimNone rs' with
        | nil => simp [trimNone, h1, h2] at h
        | cons t' ts' =>
            simp [trimNone, h1, h2] at h
            rw [h.1, h.2]
  · -- 头非空白：两边都等于 `r :: trim 尾部`
    rw [trimNone_cons_of_ne hr, trimNone_cons_of_ne hr] at h
    exact (List.cons.inj h).2

/-- 头部为空白时的展开式（去掉内部 `if`）。 -/
theorem trimNone_none_cons (rs : List Sym) :
    trimNone (none :: rs) =
      (match trimNone rs with
       | [] => []
       | t => none :: t) := by
  change (match trimNone rs with
          | [] => if none = none then [] else [none]
          | t => none :: t) = _
  cases trimNone rs <;> simp

/-- 尾部 trim 相等时，同头加一格的 trim 也相等。 -/
theorem trimNone_cons_congr (s : Sym) {rs rs' : List Sym}
    (h : trimNone rs = trimNone rs') :
    trimNone (s :: rs) = trimNone (s :: rs') := by
  by_cases hs : s = none
  · subst hs
    rw [trimNone_none_cons, trimNone_none_cons, h]
  · rw [trimNone_cons_of_ne hs, trimNone_cons_of_ne hs, h]

/-- 列表的 `headD` 与 trim 后的 `headD` 相同。 -/
theorem headD_trimNone (l : List Sym) :
    l.headD none = (trimNone l).headD none := by
  cases l with
  | nil => rfl
  | cons a as =>
      by_cases ha : a = none
      · subst ha
        rw [trimNone_none_cons]
        cases trimNone as <;> rfl
      · rw [trimNone_cons_of_ne ha]
        rfl

/-- 读出符号只由 trim 后的列表决定：trim 相等则 `headD` 相等。 -/
theorem headD_eq_of_trimNone_eq {l l' : List Sym}
    (h : trimNone l = trimNone l') : l.headD none = l'.headD none := by
  rw [headD_trimNone l, headD_trimNone l', h]

end Tape

namespace Tape

/-- 空白填充等价：两端允许多余空白格，读写语义相同。 -/
def equiv (t u : Tape) : Prop :=
  trimNone t.left = trimNone u.left ∧ t.read = u.read ∧ trimNone t.right = trimNone u.right

/-- 等价保持读出符号。 -/
theorem equiv_read {t u : Tape} (h : equiv t u) : t.read = u.read := h.2.1

/-- `equiv` 自反。 -/
theorem equiv_refl (t : Tape) : equiv t t := ⟨rfl, rfl, rfl⟩

/-- `equiv` 对称。 -/
theorem equiv_symm {t u : Tape} (h : equiv t u) : equiv u t :=
  ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩

/-- `equiv` 传递。 -/
theorem equiv_trans {t u v : Tape} (h1 : equiv t u) (h2 : equiv u v) : equiv t v :=
  ⟨h1.1.trans h2.1, h1.2.1.trans h2.2.1, h1.2.2.trans h2.2.2⟩

/-- 规范化 `canon` 与原纸带等价（右侧只差一个尾部空白）。 -/
theorem equiv_canon (t : Tape) : equiv (canon t) t := by
  obtain ⟨l, r⟩ := t
  cases r with
  | nil =>
      -- 右侧为空：规范化补一个空白，读写语义不变
      simp [canon, equiv, Tape.read, trimNone]
  | cons a rest =>
      -- 右侧非空：规范化不改动
      simp [canon, equiv, Tape.read]

/-- 写入后右侧 trim 相等（尾部可能不同但都只剩空白）。 -/
theorem trimNone_write_cons {r r' : List Sym} (s : Sym)
    (hread : r.headD none = r'.headD none)
    (h : trimNone r = trimNone r') :
    trimNone (s :: r.tail) = trimNone (s :: r'.tail) := by
  rcases r with _ | ⟨a, as⟩ <;> rcases r' with _ | ⟨b, bs⟩
  · rfl
  · -- 左侧为空、右侧非空：右侧头必为空白
    have hb : b = none := by simpa using hread.symm
    subst hb
    have hz : trimNone bs = [] := by
      have hh : trimNone (none :: bs) = trimNone ([] : List Sym) := by
        simpa using h.symm
      exact (trimNone_none_cons_eq_nil).mp hh
    exact trimNone_cons_congr s hz.symm
  · -- 对称
    have ha : a = none := by simpa using hread
    subst ha
    have hz : trimNone as = [] := by
      have hh : trimNone (none :: as) = trimNone ([] : List Sym) := by
        simpa using h
      exact (trimNone_none_cons_eq_nil).mp hh
    exact trimNone_cons_congr s hz
  · -- 两侧都非空
    have hab : a = b := by simpa using hread
    subst hab
    exact trimNone_cons_congr s (trimNone_cons_inj a h)

/-- 写入保持纸带等价。 -/
theorem equiv_write {t u : Tape} (h : equiv t u) (s : Sym) :
    equiv (t.write s) (u.write s) := by
  rcases h with ⟨hl, hread, hr⟩
  refine ⟨hl, ?_, ?_⟩
  · -- 读出：写入后两台机器都读到 s
    show (s :: t.right.tail).headD none = (s :: u.right.tail).headD none
    rfl
  · -- 右侧：写入后 trim 仍相等
    show trimNone (s :: t.right.tail) = trimNone (s :: u.right.tail)
    exact trimNone_write_cons s hread hr

/-- 右移保持纸带等价。 -/
theorem equiv_moveRight {t u : Tape} (h : equiv t u) :
    equiv t.moveRight u.moveRight := by
  rcases h with ⟨hl, hread, hr⟩
  rcases ht : t.right with _ | ⟨r1, rs1⟩ <;> rcases hu : u.right with _ | ⟨r2, rs2⟩
  · -- 两侧右侧都为空：右移都在左边补空白
    simp only [Tape.moveRight, ht, hu]
    exact ⟨trimNone_cons_congr none hl, rfl, rfl⟩
  · -- 左侧空、右侧非空
    have hr2 : r2 = none := by
      have hh := hread
      simp [Tape.read, ht, hu] at hh
      exact hh.symm
    subst hr2
    have hz : trimNone rs2 = [] := by
      have hh : trimNone (none :: rs2) = [] := by
        have hh0 := hr
        simp [ht, hu] at hh0
        exact hh0.symm
      exact (trimNone_none_cons_eq_nil).mp hh
    simp only [Tape.moveRight, ht, hu]
    refine ⟨trimNone_cons_congr none hl, ?_, hz.symm⟩
    · show none = rs2.headD none
      exact headD_eq_of_trimNone_eq (l := []) (l' := rs2) hz.symm
  · -- 左侧非空、右侧空
    have hr1 : r1 = none := by
      have hh := hread
      simp [Tape.read, ht, hu] at hh
      exact hh
    subst hr1
    have hz : trimNone rs1 = [] := by
      have hh : trimNone (none :: rs1) = [] := by
        have hh0 := hr
        simp [ht, hu] at hh0
        exact hh0
      exact (trimNone_none_cons_eq_nil).mp hh
    simp only [Tape.moveRight, ht, hu]
    refine ⟨trimNone_cons_congr none hl, ?_, hz⟩
    · show rs1.headD none = none
      exact headD_eq_of_trimNone_eq (l := rs1) (l' := []) hz
  · -- 两侧都非空
    have h12 : r1 = r2 := by
      have hh := hread
      simp [Tape.read, ht, hu] at hh
      exact hh
    subst h12
    have htails : trimNone rs1 = trimNone rs2 := by
      have hh : trimNone (r1 :: rs1) = trimNone (r1 :: rs2) := by
        simpa [ht, hu] using hr
      exact trimNone_cons_inj r1 hh
    simp only [Tape.moveRight, ht, hu]
    refine ⟨trimNone_cons_congr r1 hl, ?_, htails⟩
    · show rs1.headD none = rs2.headD none
      exact headD_eq_of_trimNone_eq htails

/-- 左移保持纸带等价。 -/
theorem equiv_moveLeft {t u : Tape} (h : equiv t u) :
    equiv t.moveLeft u.moveLeft := by
  rcases h with ⟨hl, hread, hr⟩
  rcases ht : t.left with _ | ⟨l1, ls1⟩ <;> rcases hu : u.left with _ | ⟨l2, ls2⟩
  · -- 两侧左侧都为空：左移都在右边补空白
    simp only [Tape.moveLeft, ht, hu]
    exact ⟨rfl, rfl, trimNone_cons_congr none hr⟩
  · -- 左侧空、右侧非空
    have h0 : trimNone (l2 :: ls2) = [] := by
      have hh : trimNone (l2 :: ls2) = trimNone ([] : List Sym) := by
        simpa [ht, hu] using hl.symm
      exact hh
    have hl2 : l2 = none := (trimNone_eq_nil_iff).mp h0 l2 List.mem_cons_self
    subst hl2
    have hz : trimNone ls2 = [] := (trimNone_none_cons_eq_nil).mp h0
    simp only [Tape.moveLeft, ht, hu]
    exact ⟨hz.symm, rfl, trimNone_cons_congr none hr⟩
  · -- 左侧非空、右侧空
    have h0 : trimNone (l1 :: ls1) = [] := by
      have hh : trimNone (l1 :: ls1) = trimNone ([] : List Sym) := by
        simpa [ht, hu] using hl
      exact hh
    have hl1 : l1 = none := (trimNone_eq_nil_iff).mp h0 l1 List.mem_cons_self
    subst hl1
    have hz : trimNone ls1 = [] := (trimNone_none_cons_eq_nil).mp h0
    simp only [Tape.moveLeft, ht, hu]
    exact ⟨hz, rfl, trimNone_cons_congr none hr⟩
  · -- 两侧都非空
    have hheads : l1 = l2 := by
      have hh : trimNone (l1 :: ls1) = trimNone (l2 :: ls2) := by
        simpa [ht, hu] using hl
      exact headD_eq_of_trimNone_eq hh
    subst hheads
    have htails : trimNone ls1 = trimNone ls2 := by
      have hh : trimNone (l1 :: ls1) = trimNone (l1 :: ls2) := by
        simpa [ht, hu] using hl
      exact trimNone_cons_inj l1 hh
    simp only [Tape.moveLeft, ht, hu]
    exact ⟨htails, rfl, trimNone_cons_congr l1 hr⟩

/-- 任意方向移动都保持纸带等价。 -/
theorem equiv_move {t u : Tape} (d : Dir) (h : equiv t u) :
    equiv (t.move d) (u.move d) := by
  cases d
  · exact equiv_moveLeft h
  · exact equiv_moveRight h
  · exact h

end Tape

namespace DTM

variable {q : Nat}

/-- 单步保持「状态相等 + 纸带等价」。 -/
theorem stepConfig_equiv (M : DTM q) {c c' : Config q}
    (hs : c.state = c'.state) (ht : Tape.equiv c.tape c'.tape) :
    (M.stepConfig c).state = (M.stepConfig c').state ∧
      Tape.equiv (M.stepConfig c).tape (M.stepConfig c').tape := by
  have hread : c.tape.read = c'.tape.read := Tape.equiv_read ht
  simp only [DTM.stepConfig, hs, hread]
  refine ⟨trivial, ?_⟩
  rcases hstep : M.step c'.state c'.tape.read with ⟨q', s, d⟩
  simp only [hstep]
  exact Tape.equiv_move d (Tape.equiv_write ht s)

/-- 停机判定只看状态：状态相等则停机判断相等。 -/
theorem halted_congr (M : DTM q) {c c' : Config q} (hs : c.state = c'.state) :
    M.halted c = M.halted c' := by
  simp only [DTM.halted, hs]

/-- 运行保持「状态相等 + 纸带等价」。 -/
theorem run_equiv (M : DTM q) (n : Nat) {c c' : Config q}
    (hs : c.state = c'.state) (ht : Tape.equiv c.tape c'.tape) :
    (M.run n c).state = (M.run n c').state ∧
      Tape.equiv (M.run n c).tape (M.run n c').tape := by
  induction n generalizing c c' with
  | zero => exact ⟨hs, ht⟩
  | succ n ih =>
      have hh := DTM.halted_congr (M := M) hs
      cases hv : M.halted c with
      | true =>
          have h' : M.halted c' = true := by rw [← hh]; exact hv
          simp only [DTM.run, hv, h']
          exact ⟨hs, ht⟩
      | false =>
          have h' : M.halted c' = false := by rw [← hh]; exact hv
          simp only [DTM.run, hv, h']
          have hstep := DTM.stepConfig_equiv (M := M) hs ht
          exact ih hstep.1 hstep.2

end DTM

end Pnp
