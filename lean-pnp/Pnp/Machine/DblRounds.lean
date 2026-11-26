/-
  文件：Pnp/Machine/DblRounds.lean
  File: Pnp/Machine/DblRounds.lean

  主题：**固定轮数的链式倍增 `dblRounds R`**。把 `dblOnce`（单机一轮倍增）用
        `seqComp` 左嵌套地串 R 份，得到一台「恰好跑 R 轮倍增、然后停机」的确定性机——
        与永不中止的 `dblChained` 互补：控制器需要「恰好 R 轮」的倍增时用本机。
  Topic: `dblRounds R` — `R` copies of `dblOnce` chained by `seqComp` (left-nested), a
  machine performing exactly `R` doubling rounds and then halting (complementary to the
  looping `dblChained`).

  接口（同 `dblOnce`，形状全程不变）：
      `⟨[none] ++ L, unary m ++ [none]⟩ → ⟨[none] ++ L, unary (m · 2^R) ++ [none]⟩`
  代价 `dblRoundsSteps R m`（按轮递归）；最后一轮后停机（accept = reject = `7R`）。
  Interface as `dblOnce`, shape preserved; cost `dblRoundsSteps R m`; halts after round `R`.

  状态数：`7 * R + 1`（`R = 0` 为 1 态立即停机；`R + 1` 为 `seqComp (dblRounds R) dblOnce`，
  左嵌套使 `(7R+1) + 7` 与 `7(R+1) + 1` 定义等价）。
  State count `7 * R + 1`; the left nesting makes the arithmetic definitional.

  本文件给出（#222）：
    - `dblRounds : (R : Nat) → DTM (7 * R + 1)`、`dblRoundsSteps`；
    - `dblRounds_accept_val` / `dblRounds_reject_val`（终止态编号 `7R`；不停机判定复用
      `Go.lean` 的 `halted_false_of_ne`）；
    - `dblRounds_no_halt`（R 轮全程不停机）与 `dblRounds_run`（整段运行规格）。
  This file gives the chained machine, its halting-state indices, the no-halt fact and
  the whole-run spec.
-/

import Pnp.Machine.DblOnce
import Pnp.Machine.SeqComp
import Pnp.Machine.Go

namespace Pnp

namespace DTM

/-- **固定轮数链式倍增**：`R = 0` 为单态立即停机；`R + 1` 为「先 R 轮、再一轮」。
    `R` chained doubling rounds: `R = 0` halts immediately, `R + 1` is `R` rounds then one. -/
def dblRounds : (R : Nat) → DTM (7 * R + 1)
  | 0 => { step := fun s a => (s, a, Dir.stay), start := 0, accept := 0, reject := 0 }
  | R + 1 => seqComp (q := 7 * R + 1) (q' := 7) (dblRounds R) dblOnce

/-- `R` 轮链式倍增的总步数（`R + 1` 轮 = 前 R 轮 + 切换 1 步 + 末轮 `dblOnce`）。
    Total step count of `R` chained doubling rounds. -/
def dblRoundsSteps : Nat → Nat → Nat
  | 0, _ => 0
  | R + 1, m => dblRoundsSteps R m + (dblOnceSteps (m * 2 ^ R) + 1)

/-- `dblRounds R` 的接受态编号为 `7 R`。 The accept state index of `dblRounds R` is `7 R`. -/
theorem dblRounds_accept_val (R : Nat) : (dblRounds R).accept.val = 7 * R := by
  induction R with
  | zero => rfl
  | succ R _ih =>
      show (Fin.natAdd (7 * R + 1) dblOnce.accept).val = 7 * (R + 1)
      rw [Fin.val_natAdd, show dblOnce.accept.val = 6 from rfl]
      omega

/-- `dblRounds R` 的拒绝态编号同样为 `7 R`。 The reject state index is also `7 R`. -/
theorem dblRounds_reject_val (R : Nat) : (dblRounds R).reject.val = 7 * R := by
  induction R with
  | zero => rfl
  | succ R _ih =>
      show (Fin.natAdd (7 * R + 1) dblOnce.reject).val = 7 * (R + 1)
      rw [Fin.val_natAdd, show dblOnce.reject.val = 6 from rfl]
      omega

/-- **R 轮链式倍增的合并规格**（运行 + 全程不停机）。两者互相依赖（不停机要知前段终态），
    故在同一个对 `R` 的归纳里一并证明。
    Combined spec of the `R`-round run and its no-halt property, proved by one induction. -/
theorem dblRounds_spec (R m : Nat) (hm : 1 ≤ m) (L : List Sym) :
    ((dblRounds R).run (dblRoundsSteps R m)
        ⟨(dblRounds R).start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩ =
      ⟨(dblRounds R).accept, Tape.mk ([none] ++ L) (unary (m * 2 ^ R) ++ [none])⟩) ∧
    (∀ k, k < dblRoundsSteps R m →
      (dblRounds R).halted
        ((dblRounds R).run k ⟨(dblRounds R).start,
          Tape.mk ([none] ++ L) (unary m ++ [none])⟩) = false) := by
  induction R generalizing m with
  | zero =>
      refine ⟨?_, ?_⟩
      · have h1 : m * 2 ^ 0 = m := by rw [Nat.pow_zero, Nat.mul_one]
        rw [h1]
        rfl
      · intro k hk
        simp [dblRoundsSteps] at hk
  | succ R ih =>
      -- 组合机 = `seqComp (dblRounds R) dblOnce`；总步数写成 `前段 + 1 + 末段`
      have hsteps : dblRoundsSteps (R + 1) m
          = dblRoundsSteps R m + 1 + dblOnceSteps (m * 2 ^ R) := by
        rw [show dblRoundsSteps (R + 1) m
            = dblRoundsSteps R m + (dblOnceSteps (m * 2 ^ R) + 1) from rfl]
        omega
      -- 前段起点纸带（= 整段起点）、末段起点纸带（= 前段终点）
      have hnhA : ∀ k, k < dblRoundsSteps R m →
          (dblRounds R).halted ((dblRounds R).run k
            ⟨(dblRounds R).start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩) = false :=
        (ih m hm).2
      -- 末轮输入值 `m · 2^R ≥ 1`（`dblOnce` 的前提）
      have hmR : 1 ≤ m * 2 ^ R :=
        Nat.succ_le_of_lt (Nat.mul_pos (by omega) (Nat.pow_pos (by decide : 0 < 2)))
      have hnhB : ∀ k, k < dblOnceSteps (m * 2 ^ R) → dblOnce.halted
          (dblOnce.run k ⟨dblOnce.start,
            Tape.mk ([none] ++ L) (unary (m * 2 ^ R) ++ [none])⟩) = false :=
        dblOnce_no_halt (m * 2 ^ R) hmR L
      -- 末段起点纸带右侧非空（切换步不改纸带的前提）
      have hneT : (Tape.mk ([none] ++ L) (unary (m * 2 ^ R) ++ [none])).right ≠ [] := by
        intro hh
        cases (List.append_eq_nil_iff.mp hh).2
      have hval : m * 2 ^ (R + 1) = (m * 2 ^ R) + (m * 2 ^ R) := by
        rw [Nat.pow_succ, ← Nat.mul_assoc, Nat.mul_two]
      refine ⟨?_, ?_⟩
      · -- 运行规格：`seqComp_run` 拼「前 R 轮 + 切换 + 末轮」
        rw [hsteps, hval]
        exact seqComp_run (dblRounds R) dblOnce (dblRoundsSteps R m)
          (dblOnceSteps (m * 2 ^ R))
          ⟨(dblRounds R).start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩
          (Tape.mk ([none] ++ L) (unary (m * 2 ^ R) ++ [none]))
          (Tape.mk ([none] ++ L) (unary ((m * 2 ^ R) + (m * 2 ^ R)) ++ [none]))
          (ih m hm).1 hneT
          (dblOnce_run (m * 2 ^ R) hmR L) hnhA hnhB
      · -- 不停机：按 `k` 落点分三段（前段 / 恰在交界 / 末段）
        intro k hk
        show (seqComp (dblRounds R) dblOnce).halted
          ((seqComp (dblRounds R) dblOnce).run k
            ⟨Fin.castAdd 7 (dblRounds R).start,
              Tape.mk ([none] ++ L) (unary m ++ [none])⟩) = false
        rw [hsteps] at hk
        by_cases hk1 : k < dblRoundsSteps R m
        · -- ① 仍在前 R 轮内：状态在左段，终止态在右段，永不命中
          rw [seqComp_embed_left (dblRounds R) dblOnce k
            ⟨(dblRounds R).start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩
            (fun j hj => hnhA j (Nat.lt_trans hj hk1))]
          exact halted_false_of_ne (seqComp (dblRounds R) dblOnce) _
            (seqComp_halt_castAdd (dblRounds R) dblOnce _).1.symm
            (seqComp_halt_castAdd (dblRounds R) dblOnce _).2.symm
        · by_cases hk2 : k = dblRoundsSteps R m
          · -- ② 恰在前段终点：组合机里这只是普通状态（切换步尚未发生）
            subst hk2
            rw [seqComp_embed_left (dblRounds R) dblOnce (dblRoundsSteps R m)
              ⟨(dblRounds R).start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩ hnhA,
              (ih m hm).1]
            refine halted_false_of_ne (seqComp (dblRounds R) dblOnce) _ ?_ ?_
            · intro hh
              have hv := congrArg Fin.val hh
              rw [Fin.val_castAdd, dblRounds_accept_val, seqComp_accept_val,
                show dblOnce.accept.val = 6 from rfl] at hv
              omega
            · intro hh
              have hv := congrArg Fin.val hh
              rw [Fin.val_castAdd, dblRounds_accept_val, seqComp_reject_val,
                show dblOnce.reject.val = 6 from rfl] at hv
              omega
          · -- ③ 已进入末段 `dblOnce`
            -- 拆出「前段 + 切换」与末段剩余 `j` 步
            obtain ⟨j, rfl⟩ : ∃ j, k = dblRoundsSteps R m + 1 + j :=
              ⟨k - (dblRoundsSteps R m + 1), by omega⟩
            -- 前段 + 切换步：到末段起点
            have hpre : (seqComp (dblRounds R) dblOnce).run (dblRoundsSteps R m + 1)
                ⟨Fin.castAdd 7 (dblRounds R).start,
                  Tape.mk ([none] ++ L) (unary m ++ [none])⟩
                = ⟨Fin.natAdd (7 * R + 1) dblOnce.start,
                    Tape.mk ([none] ++ L) (unary (m * 2 ^ R) ++ [none])⟩ := by
              rw [DTM.run_add (seqComp (dblRounds R) dblOnce) (dblRoundsSteps R m) 1]
              rw [seqComp_embed_left (dblRounds R) dblOnce (dblRoundsSteps R m)
                ⟨(dblRounds R).start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩ hnhA,
                (ih m hm).1]
              rw [seqComp_switch (dblRounds R) dblOnce
                ⟨(dblRounds R).accept,
                  Tape.mk ([none] ++ L) (unary (m * 2 ^ R) ++ [none])⟩ rfl]
              rw [show ((Tape.mk ([none] ++ L) (unary (m * 2 ^ R) ++ [none])).write
                    (Tape.mk ([none] ++ L) (unary (m * 2 ^ R) ++ [none])).read).move
                    Dir.stay
                  = Tape.mk ([none] ++ L) (unary (m * 2 ^ R) ++ [none]) from by
                rw [Tape.move, Tape.write_read _ hneT]]
            -- 末段 `j` 步的搬运
            rw [DTM.run_add (seqComp (dblRounds R) dblOnce) (dblRoundsSteps R m + 1) j,
              hpre]
            rw [seqComp_embed_right (dblRounds R) dblOnce j
              ⟨dblOnce.start, Tape.mk ([none] ++ L) (unary (m * 2 ^ R) ++ [none])⟩
              (fun i hi => hnhB i (by omega))]
            -- 末段内部未停机 ⇒ 其状态既非接受也非拒绝
            have hnhj : dblOnce.halted
                (dblOnce.run j ⟨dblOnce.start,
                  Tape.mk ([none] ++ L) (unary (m * 2 ^ R) ++ [none])⟩) = false :=
              hnhB j (by omega)
            have ⟨hna, hnr⟩ : (dblOnce.run j ⟨dblOnce.start,
                  Tape.mk ([none] ++ L) (unary (m * 2 ^ R) ++ [none])⟩).state ≠ dblOnce.accept
                ∧ (dblOnce.run j ⟨dblOnce.start,
                  Tape.mk ([none] ++ L) (unary (m * 2 ^ R) ++ [none])⟩).state ≠ dblOnce.reject := by
              rw [DTM.halted, Bool.or_eq_false_iff] at hnhj
              exact ⟨beq_eq_false_iff_ne.mp hnhj.1, beq_eq_false_iff_ne.mp hnhj.2⟩
            exact halted_false_of_ne (seqComp (dblRounds R) dblOnce) _
              (seqComp_halt_natAdd (dblRounds R) dblOnce _ hna hnr).1.symm
              (seqComp_halt_natAdd (dblRounds R) dblOnce _ hna hnr).2.symm

/-- **R 轮链式倍增整段运行**：形状不变，值 `m ↦ m · 2^R`，末态为终止态。
    The whole `R`-round run: shape preserved, `m ↦ m · 2^R`, ending at the final state. -/
theorem dblRounds_run (R m : Nat) (hm : 1 ≤ m) (L : List Sym) :
    (dblRounds R).run (dblRoundsSteps R m)
      ⟨(dblRounds R).start, Tape.mk ([none] ++ L) (unary m ++ [none])⟩ =
    ⟨(dblRounds R).accept, Tape.mk ([none] ++ L) (unary (m * 2 ^ R) ++ [none])⟩ :=
  (dblRounds_spec R m hm L).1

/-- **R 轮全程不停机**（`dblRounds R` 只在最后一轮结束后才停机）。
    `dblRounds R` never halts before the very last step. -/
theorem dblRounds_no_halt (R m : Nat) (hm : 1 ≤ m) (L : List Sym) :
    ∀ k, k < dblRoundsSteps R m →
      (dblRounds R).halted
        ((dblRounds R).run k ⟨(dblRounds R).start,
          Tape.mk ([none] ++ L) (unary m ++ [none])⟩) = false :=
  (dblRounds_spec R m hm L).2

end DTM

end Pnp
