import Lake
open Lake DSL

package "diophantine_floor" where
  version := v!"1.0.0"
  keywords := #["mathematics", "physics", "formal-verification", "lean4", "diophantine-floor", "mass-gap"]
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.34.0"

@[default_target]
lean_lib «DiophantineFloor» where
  roots := #[`DiophantineFloor]
