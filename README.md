# Reservoir Seismicity Control

This repository contains supporting material for the manuscript:

**Control of Human-Induced Seismicity in Underground Reservoirs Governed by a Nonlinear PDE–ODE System**

## Description

The work studies feedback control of underground reservoir operations to
reduce induced seismicity while satisfying operational constraints. The
mathematical model couples a pressure-diffusion PDE with a nonlinear
seismicity-rate ODE. The Groningen gas field is used as a numerical
case study.

## Repository contents

- [Lean formalization](lean/): Lean 4 source and
  [build instructions](lean/README.md).
- [Verification audit](lean/AUDIT.md): build status, scope and assumptions.
- [Manuscript-to-proof map](lean/PAPER_MAP.md): verification entrypoints.
- [Third-party notices](THIRD_PARTY_NOTICES.md): upstream license and
  attribution for the vendored semigroup modules.

Numerical simulation code, figures and additional supporting material
may be added later.

## Funding

This work is supported by the European Research Council through the
ERC-INJECT project (Grant No. 101087771).
