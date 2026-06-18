import Lake
open Lake DSL

package «quantum-dust» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

-- The machine-checked core of *Quantum Dust from the Curse of Dimensionality*.
-- Every result asserted "proved" in the paper lives here and passes `#print axioms`
-- with only [propext, Classical.choice, Quot.sound]. Self-contained: nothing here
-- imports outside `proofs` and Mathlib.
@[default_target]
lean_lib proofs where
  globs := #[.submodules `proofs]
