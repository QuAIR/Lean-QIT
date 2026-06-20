# Lean-QIT
Lean-QIT is a Lean 4 library for formally verified quantum information theory.
## What's Lean-QIT?
Lean-QIT provides reusable definitions, source-backed statements, and proof
infrastructure for quantum information theory in Lean. It is built on Mathlib,
with public theorem endpoints organized so readers and agents can import the
modules they need and compare statements against cited references.
### Aims
- Provide a modest, reusable Lean library for finite-dimensional QIT.
- Keep information-theoretic statements tied to source references and stable
  import paths.
- Support source-first public statements whose Lean declarations can be audited
  against the cited mathematical literature.
- Keep public statements, source evidence, and Lean proof-status alignment as
  separate auditable records.
## Using Lean-QIT in your project
To add Lean-QIT as a dependency to a Lake project, add this to `lakefile.toml`:
```toml
[[require]]
name = "QIT"
git = "https://github.com/QuAIR/Lean-QIT.git"
rev = "main"
```
Use the Lean version pinned by `lean-toolchain`. Then import either the
aggregate module or a focused module:
```lean
import QIT
import QIT.Core
import QIT.Information
import QIT.Nonlocality
import QIT.Security
```
The library currently includes:
- `QIT.Core`: finite-dimensional systems, states, channels, measurements, Bell
  scenarios, trace-norm support, purification, and self-testing.
- `QIT.Util`: matrix and block-matrix utilities.
- `QIT.Classical`: classical and classical-quantum interface bridges.
- `QIT.Information`: entropy, Renyi, smooth-entropy, typicality, recovery, and asymptotic information-theory interfaces.
- `QIT.Entanglement`: separability and PPT-oriented definitions.
- `QIT.Nonlocality`: Bell scenario, CHSH, Tsirelson, and certification entry points.
- `QIT.Security`: BB84, key security, and randomness-extractor interfaces.
For a quick build check:
```bash
lake exe cache get
lake build QIT
```
For theorem discovery, start from `QIT.lean` or the module names above. Lean
docstrings cite source references using keys resolved by `REFERENCES.json`.
## License
Lean-QIT is released under the Apache License 2.0. See `LICENSE`.
