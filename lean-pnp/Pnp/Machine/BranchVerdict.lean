/-
  文件：Pnp/Machine/BranchVerdict.lean
  File: Pnp/Machine/BranchVerdict.lean

  主题：E 外层循环的**判定布尔量**——「计数器 `j` 对应的分支是否让逐分支判定机接受」。
  Topic: the Boolean verdict of E's outer loop for the branch decoded from counter `j`.

  用法：`branchAcceptB` 把逐分支判定机的接受判定变成 `Bool`，`branchAny_iff_acceptsWithin`
  再把它对 `List.range (T·B^T)` 取 `any`，得到 E 的判定规格
  「任一分支命中 ⇔ 原机 `T` 步内接受」。
  Usage: `branchAcceptB` turns the per-branch acceptance into a Boolean; taking `any`
  over the counter range yields E's verdict specification.
-/

import Pnp.Machine.BranchMachineTwo
import Pnp.Machine.BranchIndex

namespace Pnp

namespace DTM

/-- 计数器 `j` 的分支判定：逐分支判定机跑满统一预算后是否停在接受态。
    Boolean verdict of the branch decoded from counter `j`. -/
def branchAcceptB {q : Nat} (M : NTM q) (w : List Bool) (a : Sym) (l' : List Sym)
    (B T b Z : Nat) (R : List Sym) (j : Nat) : Bool :=
  decide (((seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
          (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).run
        (expandCost (a :: l') + 1
          + ((padStr (branchPad M.start w Z T B b - 1)).length + 1
            + (3 * branchPad M.start w Z T B b + 3 * l'.length + 1 + 1 + 1)) + 1
          + (roundCostStay (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)) Z B
                (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)).cur
              + branchBudget (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)).pre.length
                  Z T B b))
        ⟨(seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
            (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
            (obsPhase q b ((M.stutter).haltNorm))).start,
          Tape.mk (padStr T ++ (none :: List.replicate Z (some false)
              ++ digitArea ((branchOfIndex B T j).2 % B :: branchBlocks B (branchOfIndex B T j).1 (branchOfIndex B T j).2)))
            ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
              ++ (List.replicate (padStr (branchPad M.start w Z T B b - 1)).length none ++ R))⟩).state
      = (seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
          (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).accept)

/-- `branchAcceptB` 的真假与接受态判定一致。 -/
theorem branchAcceptB_iff {q : Nat} (M : NTM q) (w : List Bool) (a : Sym) (l' : List Sym)
    (B T b Z : Nat) (R : List Sym) (j : Nat) :
    branchAcceptB M w a l' B T b Z R j = true ↔
      (((seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
          (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).run
        (expandCost (a :: l') + 1
          + ((padStr (branchPad M.start w Z T B b - 1)).length + 1
            + (3 * branchPad M.start w Z T B b + 3 * l'.length + 1 + 1 + 1)) + 1
          + (roundCostStay (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)) Z B
                (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)).cur
              + branchBudget (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)).pre.length
                  Z T B b))
        ⟨(seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
            (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
            (obsPhase q b ((M.stutter).haltNorm))).start,
          Tape.mk (padStr T ++ (none :: List.replicate Z (some false)
              ++ digitArea ((branchOfIndex B T j).2 % B :: branchBlocks B (branchOfIndex B T j).1 (branchOfIndex B T j).2)))
            ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
              ++ (List.replicate (padStr (branchPad M.start w Z T B b - 1)).length none ++ R))⟩).state
      = (seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
          (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).accept) := by
  by_cases h : (
((seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
          (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).run
        (expandCost (a :: l') + 1
          + ((padStr (branchPad M.start w Z T B b - 1)).length + 1
            + (3 * branchPad M.start w Z T B b + 3 * l'.length + 1 + 1 + 1)) + 1
          + (roundCostStay (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)) Z B
                (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)).cur
              + branchBudget (Reg.initReg M.start w (T + 1) (branchPad M.start w Z T B b)).pre.length
                  Z T B b))
        ⟨(seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
            (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
            (obsPhase q b ((M.stutter).haltNorm))).start,
          Tape.mk (padStr T ++ (none :: List.replicate Z (some false)
              ++ digitArea ((branchOfIndex B T j).2 % B :: branchBlocks B (branchOfIndex B T j).1 (branchOfIndex B T j).2)))
            ((a :: l') ++ List.replicate (2 * (a :: l').length + 1) none
              ++ (List.replicate (padStr (branchPad M.start w Z T B b - 1)).length none ++ R))⟩).state
      = (seqComp (alignChain (padStr (branchPad M.start w Z T B b - 1))
          (3 * branchPad M.start w Z T B b + 3 * l'.length + 1))
          (obsPhase q b ((M.stutter).haltNorm))).accept)
  · simp [branchAcceptB, h]
  · simp [branchAcceptB, h]

set_option maxHeartbeats 4000000 in
/-- **E 的判定规格**：在计数器 `j < T·B^T` 上取 `any`，为真当且仅当原机 `T` 步内接受。
    E's verdict specification: `any` of the per-branch verdicts over the counter range
    is true iff `M` accepts within `T` steps. -/
theorem branchAny_iff_acceptsWithin {q : Nat} (M : NTM q) (w : List Bool) (a : Sym)
    (l' : List Sym) (hw : w.map some = a :: l') (hl : ∀ v ∈ a :: l', v ≠ none)
    {B : Nat} (hB : ∀ s x', (M.step s x').length ≤ B) (hBpos : 0 < B)
    (T b : Nat) (hbnd : B + 2 < 2 ^ b) (hT : 0 < T) (Z : Nat) (hZT : Z ≤ T + 1)
    (R : List Sym) (hxacc : M.start ≠ M.accept) (hxre : M.start ≠ M.reject) :
    (List.range (T * B ^ T)).any (fun j => branchAcceptB M w a l' B T b Z R j) = true ↔
      M.AcceptsWithin w T := by
  rw [any_range_iff_exists]
  have hidx := branchMachine_dummy_iff_two_index M w a l' hw hl hB hBpos T b hbnd hT Z hZT R
    hxacc hxre
  constructor
  · rintro ⟨j, hj, hP⟩
    exact hidx.mp ⟨j, hj, (branchAcceptB_iff M w a l' B T b Z R j).mp hP⟩
  · intro hacc
    obtain ⟨j, hj, heq⟩ := hidx.mpr hacc
    exact ⟨j, hj, (branchAcceptB_iff M w a l' B T b Z R j).mpr heq⟩

end DTM

end Pnp
