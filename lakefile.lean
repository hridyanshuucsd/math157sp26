import Lake
open Lake DSL

package «SpernerBrouwer» where
  name := "SpernerBrouwer"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_lib «SpernerBrouwer» where
  roots := #[`SpernerBrouwer]
