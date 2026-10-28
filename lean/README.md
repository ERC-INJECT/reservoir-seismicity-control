# ReservoirSeismicityControl — Lean 4 formalization

Companion Lean 4 proof project for **Control of Human-Induced Seismicity
in Underground Reservoirs Governed by a Nonlinear PDE–ODE System**.

The project is named after the general reservoir PDE–ODE problem, rather
than only the Groningen numerical case study.

## Scope

The published source consists of **399 ReservoirSeismicityControl Lean
modules** and **18 vendored MarkovProcess modules** (417 Lean files).

The four final verification entrypoints are:

1. `ReservoirSeismicityControl.Paper2026.PhysicalA7A10FullPhysicalFromGreen20261027`
2. `ReservoirSeismicityControl.Paper2026.VerificationSpatialNDRestrictedSmooth20261027`
3. `ReservoirSeismicityControl.Paper2026.PhysicalPressureNDA10PositiveRealization20261027`
4. `ReservoirSeismicityControl.PaperFinalCertificatesAudit`

Consult [PAPER_MAP.md](PAPER_MAP.md) and [AUDIT.md](AUDIT.md) for
the associated results, verification status and limitations.

## Reproduce the build

- Lean: `leanprover/lean4:v4.35.0-rc4`
- Mathlib: pinned in `lake-manifest.json`

From this **`lean/` directory**, with Lean/Elan and Lake installed:

```bash
lake exe cache get

lake build \
  ReservoirSeismicityControl.Paper2026.PhysicalA7A10FullPhysicalFromGreen20261027 \
  ReservoirSeismicityControl.Paper2026.VerificationSpatialNDRestrictedSmooth20261027 \
  ReservoirSeismicityControl.Paper2026.PhysicalPressureNDA10PositiveRealization20261027 \
  ReservoirSeismicityControl.PaperFinalCertificatesAudit
```

The maintainer confirmed a successful local compilation of all four
targets on **October 28, 2026**, after the namespace/measure-notation
corrections. This is a **reported local build**, not an independent
GitHub CI result. Reproduction should retain `lean-toolchain`,
`lakefile.toml` and `lake-manifest.json`. A routine build does not need
`lake update`, which may change locked dependencies.

## Mathematical limitations

A successful Lean build checks formally stated theorems under their
explicit hypotheses; it does not establish that all standard geometric,
analytic or physical hypotheses hold in a given reservoir model.

The physical A7/A10 assembly retains standard elliptic cutoff/Green
inputs and other stated assumptions. The spatial-dimension and positive
generator results retain smooth approximation and Green-identity inputs.
The complete externally cited MIMO super-twisting stability theorem,
full PDE–ODE well-posedness and automatic actuator/demand feasibility
are not independently proved by the four published targets.

## Third-party material

The 18 `MarkovProcess/Semigroup/` files are by **Scott Armstrong** and
licensed under **Apache License 2.0**. These files match upstream
[MarkovProcess](https://github.com/scottnarmstrong/MarkovProcess)
commit `666cda029098a1106914fc9fa7abd1727573284a` by Git blob SHA.
The license is included in [MarkovProcess/LICENSE](MarkovProcess/LICENSE).
See also [THIRD_PARTY_NOTICES.md](../THIRD_PARTY_NOTICES.md).

The upstream license does not establish a general license for the
original ReservoirSeismicityControl source files.
