# Quantum Dust from the Curse of Dimensionality

Machine-checked formalization and numerical reproduction suite accompanying the paper
*Quantum Dust from the Curse of Dimensionality*.

## Formalization — `proofs/`

A Lean 4 development against Mathlib. Every result the paper asserts as proved lives here and is
axiom-clean: `#print axioms` reports only `[propext, Classical.choice, Quot.sound]`, with no
`sorryAx` and no custom axioms. The results are namespaced `Verified.*` to mark them machine-verified.

```bash
lake exe cache get                      # fetch the Mathlib build cache
lake build                              # build the proofs library
lake env lean proofs/AxiomCheck.lean    # print the per-result axiom audit
```

The audit is recorded in `proofs/BUILD_AXIOM_AUDIT.log`; `FORMALIZATION.md` maps each paper label
to its Lean result.

## Numerics — `experiments/`

Python and Julia scripts reproducing the paper's measurements: the concentration law, the
relaxation / gap / band readings, and the three-structure spectral sort. `RESULTS.md` carries the
claim → reproduced-value → delta table.

```bash
python experiments/universality_sweep_cv2.py
julia  experiments/spectral_dimension.jl
```

## Layout

- `proofs/` — Lean 4 formalization (lib `proofs`, namespace `Verified.*`).
- `experiments/` — numerical reproduction (Python + Julia), with `data/`.
- `FORMALIZATION.md` — claims ledger (paper label → Lean status).
- `RESULTS.md` — numerical reproduction table.
