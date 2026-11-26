/-
  文件：lakefile.lean（Mathlib 实验工程）
  作用：在独立的 Lake 工程里引入 Mathlib v4.36.0（与本机 Lean 工具链同版本）。
        lean-pnp 保持零依赖；需要现成定理（如鸽笼原理、图灵机模型）时在本工程引用。
-/
import Lake
open Lake DSL

package pnpMathlib where

/-- 使用本地已克隆的 v4.36.0 源码（vendor/mathlib4，与工具链同版本）。
    走本地路径而不是 git 远程，是为了避免 Lake 再次全量克隆。 -/
require mathlib from "../vendor/mathlib4"

@[default_target]
lean_lib PnpMathlib where
