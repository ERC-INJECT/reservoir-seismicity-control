# Lean formalization audit

## Inventory and provenance

- Lean v4.35.0-rc4; Mathlib pinned in `lake-manifest.json`.
- 399 ReservoirSeismicityControl modules and 18 vendored MarkovProcess
  semigroup modules (417 Lean source files).
- The 18 upstream files match the corresponding files in Scott Armstrong's
  `scottnarmstrong/MarkovProcess` at commit
  `666cda029098a1106914fc9fa7abd1727573284a` by Git blob SHA.
- Generated `.lake/` data and compiled `.olean` files are excluded.

## Build status

The maintainer confirmed that the four entrypoints in [README.md](README.md)
**passed a local Lean build on October 28, 2026**. The final namespace
and qualified-measure syntax corrections were included in this build.
This is a user-reported local build; there is no independent GitHub CI
compilation claimed for this repository commit.

## Scope and limitations

Lean checks the stated results relative to their explicit hypotheses.
In particular:

- The A7/A10 assembly reuses previously established physical estimates
  and retains standard elliptic-cutoff, Green and far-field inputs.
- The `n_d = 1, 2, 3` spatial checkpoint uses the stated geometric,
  measure and smooth approximation hypotheses.
- The positive Neumann generator theorem retains smooth approximation
  and Green identity as specified inputs.
- The final audit imports finite-dimensional tracking/demand certificates;
  it does not reproduce the complete externally cited MIMO
  super-twisting stability theorem, prove overall PDE–ODE well-posedness,
  or guarantee actuator/demand feasibility without its assumptions.
- Numerical simulations and stochastic catalog validation are outside
  this Lean project.

See [PAPER_MAP.md](PAPER_MAP.md) for the direct entrypoint mapping.
