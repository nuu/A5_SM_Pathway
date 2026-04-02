import Lake
open Lake DSL

package «A5Paper3» where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "master"

@[default_target]
lean_lib «A5_SM_Pathway» where
