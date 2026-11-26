/-
  文件：Pnp/Tape.lean
  主题：纸带与单带确定性图灵机的**定义**（本文件暂不含复杂定理）。

  设计约定（与 docs/04-自建图灵机模型设计.md 一致）：
    - 字母表：Sym = Option Bool，none 表示空白，some b 表示 0/1；
    - 纸带用左右两个列表表示，右侧列表的头部就是读写头当前格；
    - 输入串放在纸带最左端，读写头初始指向第一个符号；
    - 一次转移计一步。

  当前只定义数据结构与单步语义；「判定器」「P」「NP」在后续文件实现。
-/

namespace Pnp

/-- 读写头移动方向。 -/
inductive Dir where
  | left
  | right
  | stay
  deriving DecidableEq, Repr

/-- 纸带符号：none 为空白，some true/false 为 1/0。 -/
abbrev Sym := Option Bool

/-- 纸带：left 逆序存放读写头左侧的符号，right 的头部是当前格。 -/
structure Tape where
  left  : List Sym
  right : List Sym
  deriving Repr

namespace Tape

/-- 读出当前格符号；右侧为空时视为空白。 -/
def read (t : Tape) : Sym :=
  t.right.headD none

/-- 在当前格写入符号。 -/
def write (t : Tape) (s : Sym) : Tape :=
  { t with right := s :: t.right.tail }

/-- 读写头左移一格；左侧为空时补一个空白格。 -/
def moveLeft (t : Tape) : Tape :=
  match t.left with
  | [] => { left := [], right := none :: t.right }
  | l :: ls => { left := ls, right := l :: t.right }

/-- 读写头右移一格；右侧为空时补一个空白格。 -/
def moveRight (t : Tape) : Tape :=
  match t.right with
  | [] => { left := none :: t.left, right := [] }
  | r :: rs => { left := r :: t.left, right := rs }

/-- 按方向移动。 -/
def move (t : Tape) : Dir → Tape
  | Dir.left => t.moveLeft
  | Dir.right => t.moveRight
  | Dir.stay => t

/-- 右侧非空时，读出当前符号再原样写回不改变纸带。 -/
theorem write_read (t : Tape) (h : t.right ≠ []) : t.write t.read = t := by
  cases t with
  | mk l r =>
    cases r with
    | nil => exact absurd rfl h
    | cons x xs => rfl

/-- 由输入串构造初始纸带：符号依次排列，读写头指向第一个符号。 -/
def ofInput (w : List Bool) : Tape :=
  { left := [], right := w.map some }

/-- 读回纸带右侧（从当前位置开始）的已写符号，用于取输出。 -/
def output (t : Tape) : List Sym :=
  t.right

end Tape

/-- 单带确定性图灵机：状态集为 Fin q，转移函数必须给出下一状态、写入符号与方向。 -/
structure DTM (q : Nat) where
  /-- 转移函数：当前状态与读到的符号决定下一步。 -/
  step   : Fin q → Sym → Fin q × Sym × Dir
  /-- 初始状态。 -/
  start  : Fin q
  /-- 接受状态（终止状态）。 -/
  accept : Fin q
  /-- 拒绝状态（终止状态）。 -/
  reject : Fin q

/-- 图灵机的瞬时格局：当前状态 + 纸带。 -/
structure Config (q : Nat) where
  state : Fin q
  tape  : Tape
  deriving Repr

namespace DTM

variable {q : Nat}

/-- 格局是否已进入终止状态（用 Bool 相等，便于在 if 中使用）。 -/
def halted (M : DTM q) (c : Config q) : Bool :=
  c.state == M.accept || c.state == M.reject

/-- 执行一步转移；调用方需保证当前状态不是终止状态。 -/
def stepConfig (M : DTM q) (c : Config q) : Config q :=
  let (q', s, d) := M.step c.state c.tape.read
  { state := q', tape := (c.tape.write s).move d }

/-- 至多执行 n 步；一旦进入终止状态就停止。 -/
def run (M : DTM q) : Nat → Config q → Config q
  | 0, c => c
  | n + 1, c => if M.halted c then c else M.run n (M.stepConfig c)

/-- 初始格局：从 start 状态与输入纸带出发。 -/
def init (M : DTM q) (w : List Bool) : Config q :=
  { state := M.start, tape := Tape.ofInput w }

end DTM

end Pnp
