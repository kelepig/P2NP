/-
  文件：Pnp/Machine/PadLeft.lean
  File: Pnp/Machine/PadLeft.lean

  主题：**区域左半写入机**——`seqComp writeMarkFstSnd (writeStrL (padStr T))` 的合成与整段运行。
  Topic: the left-half region writer, composed as `seqComp writeMarkFstSnd
  (writeStrL (padStr T))`, with its exact run.

  为什么用 `seqComp`（#149 教训）：手写「状态整体上移 k」的搬运引理时，`rw` 会在
  `Fin` 界的依赖证明项上触发 `motive is not type correct`；`seqComp` 的嵌入
  （`Fin.castAdd`/`Fin.natAdd`）是**函数**，`rw` 只需改写参数，安全。
  Why `seqComp`: its embeddings are plain functions, so `rw` never abstracts over
  dependent proof terms (which failed for a hand-written shift-by-k transport).

  运行结构：5 步（标记 + 当前格两符号码）+ 1 步（切换）+ `2*|padStr T|` 步（左向空白码）。
  Run: 5 steps (marker + two code symbols) + 1 switch + `2*|padStr T|` blank codes.
-/

import Pnp.Machine.SeqComp
import Pnp.Machine.WritePadL

namespace Pnp

namespace DTM

/-- **单步的显式形态**：给定一步转移的结果，`stepConfig` 就是「写入 + 移动」的显式格局。
    Explicit one-step form: given the transition result, `stepConfig` is that write+move. -/
theorem stepConfig_of_step {q : Nat} (M : DTM q) (c : Config q) (q' : Fin q) (s : Sym)
    (d : Dir) (h : M.step c.state c.tape.read = (q', s, d)) :
    M.stepConfig c = ⟨q', (c.tape.write s).move d⟩ := by
  rw [DTM.stepConfig]
  show (match M.step c.state c.tape.read with
        | (q', s, d) => ({ state := q', tape := (c.tape.write s).move d } : Config q))
      = ⟨q', (c.tape.write s).move d⟩
  rw [h]

/-- 空白码串的反转自反性（供左向写入收口）。 -/
theorem padStr_reverse (T : Nat) : (padStr T).reverse = padStr T := by
  simp [padStr]

/-- **区域左半写入机**：先跑标记相位机，再跑左向常量串写入机写 `3(T+1)` 个空白编码符号。
    用 `abbrev` 定义，使组合机的起点/终点状态在归约中透明（`rfl` 即可对齐 `seqComp`）。
    Left-half writer; `abbrev` keeps the composed start/accept transparent to reduction. -/
abbrev padLeft (T : Nat) : DTM (14 + (2 * (padStr T).length + 1)) :=
  seqComp writeMarkFstSnd (writeStrL (padStr T))

/-- 组合机在**左侧状态**上永远不停机（切换靠转移，不靠停机）。 -/
theorem padLeft_halted_left (T : Nat) (s : Fin 14) (t : Tape) :
    (padLeft T).halted ⟨Fin.castAdd _ s, t⟩ = false := by
  obtain ⟨h1, h2⟩ := seqComp_halt_castAdd writeMarkFstSnd (writeStrL (padStr T)) s
  rw [DTM.halted, Bool.or_eq_false_iff]
  exact ⟨beq_eq_false_iff_ne.mpr h1.symm, beq_eq_false_iff_ne.mpr h2.symm⟩

/-- 组合机在**右侧状态**上的停机判定，与子机一致。 -/
theorem padLeft_halted_right (T : Nat) (s : Fin (2 * (padStr T).length + 1)) (t : Tape) :
    (padLeft T).halted ⟨Fin.natAdd 14 s, t⟩
      = (writeStrL (padStr T)).halted ⟨s, t⟩ := by
  have hacc : (padLeft T).accept = Fin.natAdd 14 (writeStrL (padStr T)).accept := rfl
  have hrej : (padLeft T).reject = Fin.natAdd 14 (writeStrL (padStr T)).reject := rfl
  have hb : ∀ x y : Fin (2 * (padStr T).length + 1),
      (Fin.natAdd 14 x == Fin.natAdd 14 y) = (x == y) := by
    intro x y
    rw [Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq, Fin.ext_iff, Fin.ext_iff,
      Fin.val_natAdd, Fin.val_natAdd]
    exact ⟨Nat.add_left_cancel, fun h => by rw [h]⟩
  simp only [DTM.halted, hacc, hrej, hb]

/-- **右侧一步**：组合机在右侧的一步，正是子机一步的镜像。 -/
theorem padLeft_stepConfig_right (T : Nat) (c : Config (2 * (padStr T).length + 1)) :
    (padLeft T).stepConfig ⟨Fin.natAdd 14 c.state, c.tape⟩
      = ⟨Fin.natAdd 14 ((writeStrL (padStr T)).stepConfig c).state,
          ((writeStrL (padStr T)).stepConfig c).tape⟩ := by
  cases h : (writeStrL (padStr T)).step c.state c.tape.read with
  | mk q' sd =>
    obtain ⟨s, d⟩ := sd
    have hB : (writeStrL (padStr T)).stepConfig c
        = ⟨q', (c.tape.write s).move d⟩ := stepConfig_of_step _ c q' s d h
    have hA : (padLeft T).step (Fin.natAdd 14 c.state) c.tape.read
        = (Fin.natAdd 14 q', s, d) := by
      rw [seqComp_step_natAdd writeMarkFstSnd (writeStrL (padStr T)) c.state c.tape.read]
      rw [h]
    have hP := stepConfig_of_step (padLeft T) ⟨Fin.natAdd 14 c.state, c.tape⟩
      (Fin.natAdd 14 q') s d hA
    rw [hP, hB]

/-- **右侧整段运行搬运**：子机跑 `m` 步 ≡ 组合机从「上移 14」的格局跑 `m` 步。 -/
theorem padLeft_run_right (T : Nat) :
    ∀ (m : Nat) (c : Config (2 * (padStr T).length + 1)),
      (padLeft T).run m ⟨Fin.natAdd 14 c.state, c.tape⟩
        = ⟨Fin.natAdd 14 ((writeStrL (padStr T)).run m c).state,
            ((writeStrL (padStr T)).run m c).tape⟩ := by
  intro m
  induction m with
  | zero =>
      intro c
      rfl
  | succ m ih =>
      intro c
      have hh := padLeft_halted_right T c.state c.tape
      by_cases hc : (writeStrL (padStr T)).halted c = true
      · have hc' : (padLeft T).halted ⟨Fin.natAdd 14 c.state, c.tape⟩ = true := by
          rw [hh]; exact hc
        rw [DTM.run_of_halted (padLeft T) ⟨Fin.natAdd 14 c.state, c.tape⟩ hc',
          DTM.run_of_halted (writeStrL (padStr T)) c hc]
      · have hcf : (writeStrL (padStr T)).halted c = false := by
          cases h : (writeStrL (padStr T)).halted c <;> simp_all
        have hc' : (padLeft T).halted ⟨Fin.natAdd 14 c.state, c.tape⟩ = false := by
          rw [hh]; exact hcf
        rw [DTM.run_succ_of_not_halted _ m _ hc', DTM.run_succ_of_not_halted _ m _ hcf]
        rw [padLeft_stepConfig_right T c, ih]

/-- **区域左半写入机的运行结果**：头左侧有两格加 `3(T+1)` 格可用时，
    `6 + 2*(padStr T).length` 步后右带为 `[3(T+1) 个 false][codeFst a][codeSnd a][some true]…`。
    Exact run: the left half of the region, head resting on the leftmost written cell. -/
theorem padLeft_run (T : Nat) (a x1 x2 : Sym) (ls2 L R : List Sym)
    (hlen : ls2.length = (padStr T).length) :
    (padLeft T).run (6 + 2 * (padStr T).length)
      ⟨(padLeft T).start, Tape.mk (x1 :: x2 :: ls2 ++ L) (a :: R)⟩
      = ⟨(padLeft T).accept,
          Tape.mk L (padStr T ++ codeFst a :: codeSnd a :: some true :: R)⟩ := by
  cases a with
  | none =>
      have hmain : (padLeft T).run (6 + 2 * (padStr T).length)
            ⟨(padLeft T).start, Tape.mk (x1 :: x2 :: ls2 ++ L) (none :: R)⟩
          = ⟨(padLeft T).accept,
              Tape.mk L (padStr T ++ codeFst none :: codeSnd none :: some true :: R)⟩ := by
        show (padLeft T).run (5 + 1 + 2 * (padStr T).length) _ = _
        rw [DTM.run_add _ (5 + 1) (2 * (padStr T).length)]
        rw [DTM.run_add _ 5 1]
        show (padLeft T).run (2 * (padStr T).length)
              ((padLeft T).run 1
                ((padLeft T).run 5
                  ⟨Fin.castAdd _ (writeMarkFstSnd).start,
                    Tape.mk (x1 :: x2 :: ls2 ++ L) (none :: R)⟩)) =
              ⟨(padLeft T).accept,
                  Tape.mk L (padStr T ++ codeFst (none) :: codeSnd (none) :: some true :: R)⟩
        rw [DTM.run_succ_of_not_halted _ 4 _ (padLeft_halted_left T _ _)]
        rw [stepConfig_of_step _ _ (Fin.castAdd _ (⟨1, by omega⟩ : Fin 14)) (some true) Dir.left
              (by rw [seqComp_step_castAdd _ _ _ _ (by intro hh; have hv := congrArg Fin.val hh; simp [writeMarkFstSnd] at hv; omega)]; rfl)]
        dsimp only
        rw [show ((Tape.mk (x1 :: x2 :: ls2 ++ L) (none :: R)).write (some true)).move Dir.left = Tape.mk (x2 :: ls2 ++ L) (x1 :: some true :: R) from rfl]
        rw [DTM.run_succ_of_not_halted _ 3 _ (padLeft_halted_left T _ _)]
        rw [stepConfig_of_step _ _ (Fin.castAdd _ (⟨2, by omega⟩ : Fin 14)) (codeSnd (none)) Dir.stay
              (by rw [seqComp_step_castAdd _ _ _ _ (by intro hh; have hv := congrArg Fin.val hh; simp [writeMarkFstSnd] at hv; omega)]; rfl)]
        dsimp only
        rw [show ((Tape.mk (x2 :: ls2 ++ L) (x1 :: some true :: R)).write (codeSnd (none))).move Dir.stay = Tape.mk (x2 :: ls2 ++ L) (codeSnd (none) :: some true :: R) from rfl]
        rw [DTM.run_succ_of_not_halted _ 2 _ (padLeft_halted_left T _ _)]
        rw [stepConfig_of_step _ _ (Fin.castAdd _ (⟨3, by omega⟩ : Fin 14)) (codeSnd (none)) Dir.left
              (by rw [seqComp_step_castAdd _ _ _ _ (by intro hh; have hv := congrArg Fin.val hh; simp [writeMarkFstSnd] at hv; omega)]; rfl)]
        dsimp only
        rw [show ((Tape.mk (x2 :: ls2 ++ L) (codeSnd (none) :: some true :: R)).write (codeSnd (none))).move Dir.left = Tape.mk (ls2 ++ L) (x2 :: codeSnd (none) :: some true :: R) from rfl]
        rw [DTM.run_succ_of_not_halted _ 1 _ (padLeft_halted_left T _ _)]
        rw [stepConfig_of_step _ _ (Fin.castAdd _ (⟨4, by omega⟩ : Fin 14)) (codeFst (none)) Dir.stay
              (by rw [seqComp_step_castAdd _ _ _ _ (by intro hh; have hv := congrArg Fin.val hh; simp [writeMarkFstSnd] at hv; omega)]; rfl)]
        dsimp only
        rw [show ((Tape.mk (ls2 ++ L) (x2 :: codeSnd (none) :: some true :: R)).write (codeFst (none))).move Dir.stay = Tape.mk (ls2 ++ L) (codeFst (none) :: codeSnd (none) :: some true :: R) from rfl]
        rw [DTM.run_succ_of_not_halted _ 0 _ (padLeft_halted_left T _ _)]
        rw [stepConfig_of_step _ _ (Fin.castAdd _ (⟨13, by omega⟩ : Fin 14)) (codeFst (none)) Dir.stay
              (by rw [seqComp_step_castAdd _ _ _ _ (by intro hh; have hv := congrArg Fin.val hh; simp [writeMarkFstSnd] at hv; omega)]; rfl)]
        dsimp only
        rw [show ((Tape.mk (ls2 ++ L) (codeFst (none) :: codeSnd (none) :: some true :: R)).write (codeFst (none))).move Dir.stay = Tape.mk (ls2 ++ L) (codeFst (none) :: codeSnd (none) :: some true :: R) from rfl]
        rw [show (padLeft T).run 0
              ⟨Fin.castAdd _ (⟨13, by omega⟩ : Fin 14), Tape.mk (ls2 ++ L) (codeFst (none) :: codeSnd (none) :: some true :: R)⟩
              = ⟨Fin.castAdd _ (⟨13, by omega⟩ : Fin 14), Tape.mk (ls2 ++ L) (codeFst (none) :: codeSnd (none) :: some true :: R)⟩ from rfl]
        have hsw : ((Tape.mk (ls2 ++ L) (codeFst (none) :: codeSnd (none) :: some true :: R)).write (Tape.mk (ls2 ++ L) (codeFst (none) :: codeSnd (none) :: some true :: R)).read).move Dir.stay = Tape.mk (ls2 ++ L) (codeFst (none) :: codeSnd (none) :: some true :: R) := by
          rw [Tape.write_read _ (by simp)]
          rfl
        have hswitch : (padLeft T).run 1 ⟨Fin.castAdd _ (⟨13, by omega⟩ : Fin 14), Tape.mk (ls2 ++ L) (codeFst (none) :: codeSnd (none) :: some true :: R)⟩
              = ⟨Fin.natAdd 14 (writeStrL (padStr T)).start, Tape.mk (ls2 ++ L) (codeFst (none) :: codeSnd (none) :: some true :: R)⟩ := by
          simpa [hsw] using (seqComp_switch writeMarkFstSnd (writeStrL (padStr T))
            ⟨(⟨13, by omega⟩ : Fin 14), Tape.mk (ls2 ++ L) (codeFst (none) :: codeSnd (none) :: some true :: R)⟩ (by rfl))
        rw [hswitch]
        rw [padLeft_run_right T (2 * (padStr T).length)
                ⟨(writeStrL (padStr T)).start, Tape.mk (ls2 ++ L) (codeFst (none) :: codeSnd (none) :: some true :: R)⟩]
        rw [writeStrL_run (padStr T) ls2 L (codeSnd (none) :: some true :: R) (codeFst (none)) hlen]
        rw [padStr_reverse]
        rfl
      exact hmain
  | some b =>
      cases b with
      | false =>
          have hmain : (padLeft T).run (6 + 2 * (padStr T).length)
                ⟨(padLeft T).start, Tape.mk (x1 :: x2 :: ls2 ++ L) (some false :: R)⟩
              = ⟨(padLeft T).accept,
                  Tape.mk L (padStr T ++ codeFst (some false) :: codeSnd (some false) ::
                    some true :: R)⟩ := by
            show (padLeft T).run (5 + 1 + 2 * (padStr T).length) _ = _
            rw [DTM.run_add _ (5 + 1) (2 * (padStr T).length)]
            rw [DTM.run_add _ 5 1]
            show (padLeft T).run (2 * (padStr T).length)
                  ((padLeft T).run 1
                    ((padLeft T).run 5
                      ⟨Fin.castAdd _ (writeMarkFstSnd).start,
                        Tape.mk (x1 :: x2 :: ls2 ++ L) (some false :: R)⟩)) =
                  ⟨(padLeft T).accept,
                      Tape.mk L (padStr T ++ codeFst (some false) :: codeSnd (some false) :: some true :: R)⟩
            rw [DTM.run_succ_of_not_halted _ 4 _ (padLeft_halted_left T _ _)]
            rw [stepConfig_of_step _ _ (Fin.castAdd _ (⟨5, by omega⟩ : Fin 14)) (some true) Dir.left
                  (by rw [seqComp_step_castAdd _ _ _ _ (by intro hh; have hv := congrArg Fin.val hh; simp [writeMarkFstSnd] at hv; omega)]; rfl)]
            dsimp only
            rw [show ((Tape.mk (x1 :: x2 :: ls2 ++ L) (some false :: R)).write (some true)).move Dir.left = Tape.mk (x2 :: ls2 ++ L) (x1 :: some true :: R) from rfl]
            rw [DTM.run_succ_of_not_halted _ 3 _ (padLeft_halted_left T _ _)]
            rw [stepConfig_of_step _ _ (Fin.castAdd _ (⟨6, by omega⟩ : Fin 14)) (codeSnd (some false)) Dir.stay
                  (by rw [seqComp_step_castAdd _ _ _ _ (by intro hh; have hv := congrArg Fin.val hh; simp [writeMarkFstSnd] at hv; omega)]; rfl)]
            dsimp only
            rw [show ((Tape.mk (x2 :: ls2 ++ L) (x1 :: some true :: R)).write (codeSnd (some false))).move Dir.stay = Tape.mk (x2 :: ls2 ++ L) (codeSnd (some false) :: some true :: R) from rfl]
            rw [DTM.run_succ_of_not_halted _ 2 _ (padLeft_halted_left T _ _)]
            rw [stepConfig_of_step _ _ (Fin.castAdd _ (⟨7, by omega⟩ : Fin 14)) (codeSnd (some false)) Dir.left
                  (by rw [seqComp_step_castAdd _ _ _ _ (by intro hh; have hv := congrArg Fin.val hh; simp [writeMarkFstSnd] at hv; omega)]; rfl)]
            dsimp only
            rw [show ((Tape.mk (x2 :: ls2 ++ L) (codeSnd (some false) :: some true :: R)).write (codeSnd (some false))).move Dir.left = Tape.mk (ls2 ++ L) (x2 :: codeSnd (some false) :: some true :: R) from rfl]
            rw [DTM.run_succ_of_not_halted _ 1 _ (padLeft_halted_left T _ _)]
            rw [stepConfig_of_step _ _ (Fin.castAdd _ (⟨8, by omega⟩ : Fin 14)) (codeFst (some false)) Dir.stay
                  (by rw [seqComp_step_castAdd _ _ _ _ (by intro hh; have hv := congrArg Fin.val hh; simp [writeMarkFstSnd] at hv; omega)]; rfl)]
            dsimp only
            rw [show ((Tape.mk (ls2 ++ L) (x2 :: codeSnd (some false) :: some true :: R)).write (codeFst (some false))).move Dir.stay = Tape.mk (ls2 ++ L) (codeFst (some false) :: codeSnd (some false) :: some true :: R) from rfl]
            rw [DTM.run_succ_of_not_halted _ 0 _ (padLeft_halted_left T _ _)]
            rw [stepConfig_of_step _ _ (Fin.castAdd _ (⟨13, by omega⟩ : Fin 14)) (codeFst (some false)) Dir.stay
                  (by rw [seqComp_step_castAdd _ _ _ _ (by intro hh; have hv := congrArg Fin.val hh; simp [writeMarkFstSnd] at hv; omega)]; rfl)]
            dsimp only
            rw [show ((Tape.mk (ls2 ++ L) (codeFst (some false) :: codeSnd (some false) :: some true :: R)).write (codeFst (some false))).move Dir.stay = Tape.mk (ls2 ++ L) (codeFst (some false) :: codeSnd (some false) :: some true :: R) from rfl]
            rw [show (padLeft T).run 0
                  ⟨Fin.castAdd _ (⟨13, by omega⟩ : Fin 14), Tape.mk (ls2 ++ L) (codeFst (some false) :: codeSnd (some false) :: some true :: R)⟩
                  = ⟨Fin.castAdd _ (⟨13, by omega⟩ : Fin 14), Tape.mk (ls2 ++ L) (codeFst (some false) :: codeSnd (some false) :: some true :: R)⟩ from rfl]
            have hsw : ((Tape.mk (ls2 ++ L) (codeFst (some false) :: codeSnd (some false) :: some true :: R)).write (Tape.mk (ls2 ++ L) (codeFst (some false) :: codeSnd (some false) :: some true :: R)).read).move Dir.stay = Tape.mk (ls2 ++ L) (codeFst (some false) :: codeSnd (some false) :: some true :: R) := by
              rw [Tape.write_read _ (by simp)]
              rfl
            have hswitch : (padLeft T).run 1 ⟨Fin.castAdd _ (⟨13, by omega⟩ : Fin 14), Tape.mk (ls2 ++ L) (codeFst (some false) :: codeSnd (some false) :: some true :: R)⟩
                  = ⟨Fin.natAdd 14 (writeStrL (padStr T)).start, Tape.mk (ls2 ++ L) (codeFst (some false) :: codeSnd (some false) :: some true :: R)⟩ := by
              simpa [hsw] using (seqComp_switch writeMarkFstSnd (writeStrL (padStr T))
                ⟨(⟨13, by omega⟩ : Fin 14), Tape.mk (ls2 ++ L) (codeFst (some false) :: codeSnd (some false) :: some true :: R)⟩ (by rfl))
            rw [hswitch]
            rw [padLeft_run_right T (2 * (padStr T).length)
                    ⟨(writeStrL (padStr T)).start, Tape.mk (ls2 ++ L) (codeFst (some false) :: codeSnd (some false) :: some true :: R)⟩]
            rw [writeStrL_run (padStr T) ls2 L (codeSnd (some false) :: some true :: R) (codeFst (some false)) hlen]
            rw [padStr_reverse]
            rfl
          exact hmain
      | true =>
          have hmain : (padLeft T).run (6 + 2 * (padStr T).length)
                ⟨(padLeft T).start, Tape.mk (x1 :: x2 :: ls2 ++ L) (some true :: R)⟩
              = ⟨(padLeft T).accept,
                  Tape.mk L (padStr T ++ codeFst (some true) :: codeSnd (some true) ::
                    some true :: R)⟩ := by
            show (padLeft T).run (5 + 1 + 2 * (padStr T).length) _ = _
            rw [DTM.run_add _ (5 + 1) (2 * (padStr T).length)]
            rw [DTM.run_add _ 5 1]
            show (padLeft T).run (2 * (padStr T).length)
                  ((padLeft T).run 1
                    ((padLeft T).run 5
                      ⟨Fin.castAdd _ (writeMarkFstSnd).start,
                        Tape.mk (x1 :: x2 :: ls2 ++ L) (some true :: R)⟩)) =
                  ⟨(padLeft T).accept,
                      Tape.mk L (padStr T ++ codeFst (some true) :: codeSnd (some true) :: some true :: R)⟩
            rw [DTM.run_succ_of_not_halted _ 4 _ (padLeft_halted_left T _ _)]
            rw [stepConfig_of_step _ _ (Fin.castAdd _ (⟨9, by omega⟩ : Fin 14)) (some true) Dir.left
                  (by rw [seqComp_step_castAdd _ _ _ _ (by intro hh; have hv := congrArg Fin.val hh; simp [writeMarkFstSnd] at hv; omega)]; rfl)]
            dsimp only
            rw [show ((Tape.mk (x1 :: x2 :: ls2 ++ L) (some true :: R)).write (some true)).move Dir.left = Tape.mk (x2 :: ls2 ++ L) (x1 :: some true :: R) from rfl]
            rw [DTM.run_succ_of_not_halted _ 3 _ (padLeft_halted_left T _ _)]
            rw [stepConfig_of_step _ _ (Fin.castAdd _ (⟨10, by omega⟩ : Fin 14)) (codeSnd (some true)) Dir.stay
                  (by rw [seqComp_step_castAdd _ _ _ _ (by intro hh; have hv := congrArg Fin.val hh; simp [writeMarkFstSnd] at hv; omega)]; rfl)]
            dsimp only
            rw [show ((Tape.mk (x2 :: ls2 ++ L) (x1 :: some true :: R)).write (codeSnd (some true))).move Dir.stay = Tape.mk (x2 :: ls2 ++ L) (codeSnd (some true) :: some true :: R) from rfl]
            rw [DTM.run_succ_of_not_halted _ 2 _ (padLeft_halted_left T _ _)]
            rw [stepConfig_of_step _ _ (Fin.castAdd _ (⟨11, by omega⟩ : Fin 14)) (codeSnd (some true)) Dir.left
                  (by rw [seqComp_step_castAdd _ _ _ _ (by intro hh; have hv := congrArg Fin.val hh; simp [writeMarkFstSnd] at hv; omega)]; rfl)]
            dsimp only
            rw [show ((Tape.mk (x2 :: ls2 ++ L) (codeSnd (some true) :: some true :: R)).write (codeSnd (some true))).move Dir.left = Tape.mk (ls2 ++ L) (x2 :: codeSnd (some true) :: some true :: R) from rfl]
            rw [DTM.run_succ_of_not_halted _ 1 _ (padLeft_halted_left T _ _)]
            rw [stepConfig_of_step _ _ (Fin.castAdd _ (⟨12, by omega⟩ : Fin 14)) (codeFst (some true)) Dir.stay
                  (by rw [seqComp_step_castAdd _ _ _ _ (by intro hh; have hv := congrArg Fin.val hh; simp [writeMarkFstSnd] at hv; omega)]; rfl)]
            dsimp only
            rw [show ((Tape.mk (ls2 ++ L) (x2 :: codeSnd (some true) :: some true :: R)).write (codeFst (some true))).move Dir.stay = Tape.mk (ls2 ++ L) (codeFst (some true) :: codeSnd (some true) :: some true :: R) from rfl]
            rw [DTM.run_succ_of_not_halted _ 0 _ (padLeft_halted_left T _ _)]
            rw [stepConfig_of_step _ _ (Fin.castAdd _ (⟨13, by omega⟩ : Fin 14)) (codeFst (some true)) Dir.stay
                  (by rw [seqComp_step_castAdd _ _ _ _ (by intro hh; have hv := congrArg Fin.val hh; simp [writeMarkFstSnd] at hv; omega)]; rfl)]
            dsimp only
            rw [show ((Tape.mk (ls2 ++ L) (codeFst (some true) :: codeSnd (some true) :: some true :: R)).write (codeFst (some true))).move Dir.stay = Tape.mk (ls2 ++ L) (codeFst (some true) :: codeSnd (some true) :: some true :: R) from rfl]
            rw [show (padLeft T).run 0
                  ⟨Fin.castAdd _ (⟨13, by omega⟩ : Fin 14), Tape.mk (ls2 ++ L) (codeFst (some true) :: codeSnd (some true) :: some true :: R)⟩
                  = ⟨Fin.castAdd _ (⟨13, by omega⟩ : Fin 14), Tape.mk (ls2 ++ L) (codeFst (some true) :: codeSnd (some true) :: some true :: R)⟩ from rfl]
            have hsw : ((Tape.mk (ls2 ++ L) (codeFst (some true) :: codeSnd (some true) :: some true :: R)).write (Tape.mk (ls2 ++ L) (codeFst (some true) :: codeSnd (some true) :: some true :: R)).read).move Dir.stay = Tape.mk (ls2 ++ L) (codeFst (some true) :: codeSnd (some true) :: some true :: R) := by
              rw [Tape.write_read _ (by simp)]
              rfl
            have hswitch : (padLeft T).run 1 ⟨Fin.castAdd _ (⟨13, by omega⟩ : Fin 14), Tape.mk (ls2 ++ L) (codeFst (some true) :: codeSnd (some true) :: some true :: R)⟩
                  = ⟨Fin.natAdd 14 (writeStrL (padStr T)).start, Tape.mk (ls2 ++ L) (codeFst (some true) :: codeSnd (some true) :: some true :: R)⟩ := by
              simpa [hsw] using (seqComp_switch writeMarkFstSnd (writeStrL (padStr T))
                ⟨(⟨13, by omega⟩ : Fin 14), Tape.mk (ls2 ++ L) (codeFst (some true) :: codeSnd (some true) :: some true :: R)⟩ (by rfl))
            rw [hswitch]
            rw [padLeft_run_right T (2 * (padStr T).length)
                    ⟨(writeStrL (padStr T)).start, Tape.mk (ls2 ++ L) (codeFst (some true) :: codeSnd (some true) :: some true :: R)⟩]
            rw [writeStrL_run (padStr T) ls2 L (codeSnd (some true) :: some true :: R) (codeFst (some true)) hlen]
            rw [padStr_reverse]
            rfl
          exact hmain

end DTM

end Pnp
