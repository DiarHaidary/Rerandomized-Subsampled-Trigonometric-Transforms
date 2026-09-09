import Lake
open Lake DSL

package srht where
  version := v!"0.1.0"

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "db584cd6d46c92f209a44c0f1c829460d327499d"

lean_lib SparseFockFormal where
  srcDir := "vendor/sparse-fock"

@[default_target]
lean_lib SRHT where
  roots := #[`SRHT]

@[default_target]
lean_lib Challenge where
  roots := #[`Challenge]

@[default_target]
lean_lib Solution where
  roots := #[`Solution]
