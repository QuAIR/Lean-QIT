# Changelog

This file records notable changes to the public Lean-QIT package.

## [Unreleased]

## [0.1.0] - 2026-09-04

### Added

- First tagged public snapshot of the Lean-QIT library.
- Kernel-checked finite-dimensional infrastructure for states, channels, measurements,
  information quantities, one-shot methods, asymptotics, coding, protocols, symmetry,
  entanglement, nonlocality, and security.
- Public facades through `QIT.lean` and the documented layer entry points.
- Source-linked theorem catalog and machine-checked public declaration metadata.

### Verification

- Pinned Lean and mathlib to `v4.30.0`.
- Passed the cold Lean build, zero-warning gate, local-placeholder scan, public-axiom checks,
  import-layer checks, relocation-stable API checks, unit tests, and whitelist-only export gate.

### Scope boundaries

- This release is a verified library snapshot, not a claim that the quantum channel-capacity
  and decoupling program is complete.
- QRST and higher-order quantum-map milestones remain future work.
- Only catalog entries whose release evidence is complete are presented as proved public
  theorem claims.

[Unreleased]: https://github.com/QuAIR/Lean-QIT/compare/v0.1.0...main
[0.1.0]: https://github.com/QuAIR/Lean-QIT/releases/tag/v0.1.0
