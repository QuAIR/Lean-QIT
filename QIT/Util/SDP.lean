/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.SDP.PSDCone
public import QIT.Util.SDP.ConicDuality
public import QIT.Util.SDP.StrongDuality
public import QIT.Util.SDP.HermitianPSDTraceDuality

/-!
# Semidefinite-programming utilities

General SDP and conic-duality support used by QIT proof layers.
This facade is intentionally separate from the lightweight `QIT.Util` root
because some SDP support lemmas use the project matrix and state geometry APIs.
-/

@[expose] public section
