/-
  文件：lakefile.lean
  作用：Lean 4 工程（Lake）的构建描述。
  说明：
    - 包名 pnp；库名 Pnp；不引入任何外部依赖（本阶段不依赖 Mathlib）。
    - 编译入口见 Pnp.lean。
-/
import Lake
open Lake DSL

package pnp where

/-- 本工程唯一对外暴露的库，源码位于 Pnp/ 目录。 -/
@[default_target]
lean_lib Pnp where
