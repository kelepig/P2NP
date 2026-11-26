import Pnp.Classes
import Pnp.Machine.SymCode
namespace Pnp
namespace DTM
def codeFstT (s : Sym) : Sym := (symCode s).headD none
def codeSndT (s : Sym) : Sym := ((symCode s).drop 1).headD none
def wcTest (s' : Sym) (d : Dir) : DTM 9 where
  step := fun st a =>
    if st.val = 0 then (1, a, Dir.left)
    else if st.val = 1 then (2, codeSndT s', Dir.left)
    else if st.val = 2 then (3, codeFstT s', Dir.right)
    else if st.val = 3 then (4, a, Dir.right)
    else if st.val = 4 then (5, some false, d)
    else if st.val = 5 then (6, a, d)
    else if st.val = 6 then (7, a, d)
    else if st.val = 7 then (8, some true, Dir.stay)
    else (st, a, Dir.stay)
  start := 0
  accept := 8
  reject := 8
example (s' : Sym) (a b : Sym) (R : List Sym) :
    (wcTest s' Dir.right).run 1
      { state := (0 : Fin 9), tape := { left := b :: a :: R, right := some true :: [] } } =
    { state := (1 : Fin 9), tape := { left := a :: R, right := b :: some true :: [] } } := by
  rfl
example (s' : Sym) :
    (wcTest s' Dir.right).halted
      { state := (0 : Fin 9), tape := { left := [], right := [] } } = false := by
  rfl
end DTM
end Pnp
