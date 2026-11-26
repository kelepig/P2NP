/-
  文件：Pnp/TapeEncoding.lean
  主题：把纸带编码成单一符号串（B5 阶段 3c 的编码层）。

  单带模拟器需要把「被模拟的纸带 + 读写头位置」写在一段连续的纸带上。
  本文件用两个符号表示一个被模拟格：
    - 第一个符号：该格的符号（none / some false / some true）；
    - 第二个符号：是否读写头（some true 表示是，none 表示否）。
  这样无需额外的标记字母表，仍然只使用 `Sym = Option Bool`。

  已证：
    - 解码是编码的左逆：`decodeCells (encodeTape t) = cellsOfTape t`；
    - 组装回纸带时，右侧为空会被规范化为一个空白格（`canon`），
      这是编码的必然结果，后续模拟器证明会按「语义等价」而非结构相等处理。

  尚未完成：模拟器的转移函数与时间界（阶段 3c 主体）。
-/

import Pnp.Tape

namespace Pnp

namespace Tape

/-- 一个纸带格的编码：符号 + 头标记（`some true` 表示读写头）。 -/
def encCell (s : Sym) (head : Bool) : List Sym :=
  [s, if head then some true else none]

/-- 把纸带拆成「格 + 头标记」表：左侧逆序、右侧正序。 -/
def cellsOfTape (t : Tape) : List (Sym × Bool) :=
  t.left.reverse.map (fun s => (s, false)) ++
    match t.right with
    | [] => [(none, true)]
    | r :: rs => (r, true) :: rs.map (fun s => (s, false))

/-- 编码纸带：把每个格展开成两个符号。 -/
def encodeTape (t : Tape) : List Sym :=
  (cellsOfTape t).flatMap (fun p => encCell p.1 p.2)

/-- 解码：把两个符号还原成一个「格 + 头标记」。 -/
def decodeCells : List Sym → List (Sym × Bool)
  | a :: b :: rest => (a, b == some true) :: decodeCells rest
  | _ => []

/-- 把「格 + 头标记」表组装回纸带；头标记之前的格进入左侧，之后的进入右侧。 -/
def assemble : List (Sym × Bool) → Tape
  | [] => { left := [], right := [] }
  | (s, true) :: rest => { left := [], right := s :: rest.map (fun p => p.1) }
  | (s, false) :: rest =>
      let t := assemble rest
      { left := t.left ++ [s], right := t.right }

/-- 规范化：右侧为空时补一个空白格（编码总会写出头格）。 -/
def canon (t : Tape) : Tape :=
  { left := t.left, right :=
      match t.right with
      | [] => [none]
      | _ => t.right }

/-- 编码一个格后接任意串，解码结果正好是这个格再接其余部分的解码。 -/
theorem decodeCells_encCell (s : Sym) (head : Bool) (rest : List Sym) :
    decodeCells (encCell s head ++ rest) = (s, head) :: decodeCells rest := by
  cases head <;> rfl

/-- 先编码整张「格表」再解码，恢复原表。 -/
theorem decodeCells_encodeTape (t : Tape) :
    decodeCells (encodeTape t) = cellsOfTape t := by
  unfold encodeTape
  induction cellsOfTape t with
  | nil => rfl
  | cons p ps ih =>
      obtain ⟨s, head⟩ := p
      simp only [List.flatMap_cons]
      rw [decodeCells_encCell, ih]

/-- 辅助：若干非头格加一个头格及后续，组装后左侧正好是前缀的逆序。 -/
theorem assemble_prefix (xs : List Sym) (r : Sym) (rs : List Sym) :
    assemble (xs.map (fun s => (s, false)) ++
        ((r, true) :: rs.map (fun s => (s, false)))) =
      { left := xs.reverse, right := r :: rs } := by
  induction xs with
  | nil => simp [assemble, Function.comp_def]
  | cons s ss ih =>
      -- 前缀展开后，第一个格是非头格
      simp only [List.map_cons, List.cons_append]
      -- 展开 assemble 的一步（首格非头）
      change Tape.mk
          ((assemble (ss.map (fun s => (s, false)) ++
            ((r, true) :: rs.map (fun s => (s, false))))).left ++ [s])
          (assemble (ss.map (fun s => (s, false)) ++
            ((r, true) :: rs.map (fun s => (s, false))))).right =
        Tape.mk (s :: ss).reverse (r :: rs)
      rw [ih]
      simp [List.reverse_cons]

/-- 特例：头格之后没有内容。 -/
theorem assemble_prefix_nil (xs : List Sym) (r : Sym) :
    assemble (xs.map (fun s => (s, false)) ++ [(r, true)]) =
      { left := xs.reverse, right := [r] } := by
  have h := assemble_prefix xs r []
  simpa using h

/-- 组装是编码的左逆（右侧为空时规范化为一个空白格）。 -/
theorem assemble_encodeTape (t : Tape) :
    assemble (decodeCells (encodeTape t)) = canon t := by
  rw [decodeCells_encodeTape]
  unfold cellsOfTape
  rcases hr : t.right with _ | ⟨r, rs⟩
  · -- 右侧为空：编码里补了一个空白头格
    dsimp only
    rw [assemble_prefix_nil]
    unfold canon
    rw [hr]
    simp
  · -- 右侧非空：头格就是第一个符号
    dsimp only
    rw [assemble_prefix]
    unfold canon
    rw [hr]
    simp

/-- 规范化不改变当前读到的符号。 -/
theorem read_canon (t : Tape) : (canon t).read = t.read := by
  unfold canon Tape.read
  rcases h : t.right with _ | ⟨r, rs⟩ <;> simp

/-- 规范化是幂等的。 -/
theorem canon_idem (t : Tape) : canon (canon t) = canon t := by
  unfold canon
  rcases h : t.right with _ | ⟨r, rs⟩ <;> simp

/-- 规范化与写入相容：先规范化再写，等于先写再规范化。 -/
theorem write_canon (t : Tape) (s : Sym) :
    canon (t.write s) = (canon t).write s := by
  unfold canon Tape.write
  rcases h : t.right with _ | ⟨r, rs⟩ <;> simp

/-- 规范化与右移相容。左移会产生额外空白，需要更宽的「空白填充等价」，
    这里暂不声称。 -/
theorem moveRight_canon (t : Tape) :
    canon ((canon t).moveRight) = canon t.moveRight := by
  unfold canon Tape.moveRight
  rcases h : t.right with _ | ⟨r, rs⟩ <;> simp

end Tape

end Pnp
