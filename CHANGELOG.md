# Changelog

This file records notable changes to the public Lean-QIT package.

## [Unreleased]

## [0.2.0] - 2026-10-22

### Added

- Higher-order quantum-map theorem family, source-linked to Chiribella et al.
  (2008 supermaps; 2009 testers): link product of Choi operators, Choi
  composition of higher-order maps, deterministic superchannels (definition,
  Choi-matrix characterization, pre/post-isometry realization), deterministic
  finite combs (definition, causal normalization characterization,
  memory-chain realization of admissible maps), probabilistic combs and
  finite superinstruments (definition, positive-family network realization),
  and quantum N-testers (definition and physical realization).
- Twelve public theorem-catalog entries with completed fixed-order statement
  and proof-route audits; strict realization audit packets for the three
  realization endpoints.

### Verification

- Pinned Lean and mathlib to `v4.34.0`.
- Passed the cold Lean build, zero-warning gate, local-placeholder scan,
  public-axiom checks (82 declarations), import-layer checks,
  relocation-stable API checks, unit tests, the whitelist-only export gate,
  the 12-node fixed-order publication contract, and the review/publish
  theorem-site builds.

### Scope boundaries

- The remaining causal-structure composition variants (arbitrary-acyclic wire
  composition matches and comb associativity) are not part of this snapshot
  and remain future work.
- QRST milestones remain future work.
- Only catalog entries whose release evidence is complete are presented as
  proved public theorem claims.

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

[Unreleased]: https://github.com/QuAIR/Lean-QIT/compare/v0.2.0...main
[0.2.0]: https://github.com/QuAIR/Lean-QIT/compare/v0.1.0...v0.2.0
[0.1.0]: https://github.com/QuAIR/Lean-QIT/releases/tag/v0.1.0
