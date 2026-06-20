/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Core.System
public import QIT.Core.State
public import QIT.Core.PosSqrt
public import QIT.Core.Pure
public import QIT.Core.Map
public import QIT.Core.Channel
public import QIT.Core.Measurement
public import QIT.Core.MeasurementMap
public import QIT.Core.POVMProbability
public import QIT.Core.ProjectiveMeasurement
public import QIT.Core.MeasurementOverlap
public import QIT.Core.SupportProjection
public import QIT.Core.Order.Majorization
public import QIT.Core.SDP.PSDCone
public import QIT.Core.SDP.ConicDuality
public import QIT.Core.SDP.StrongDuality
public import QIT.Core.Components

/-!
# QIT core

Finite-dimensional cross-domain proof-kernel objects for local QIT development.

Topic-heavy theorem surfaces are available through public facades such as
`QIT.States`, `QIT.Information`, `QIT.Entanglement`, and `QIT.Nonlocality`.
-/

@[expose] public section
