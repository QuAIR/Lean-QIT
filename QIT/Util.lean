/-
Copyright (c) 2026 QuAIR.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QuAIR Team
-/

module

public import QIT.Util.Matrix
public import QIT.Util.Matrix.PosSqrt
public import QIT.Util.Matrix.JointDiagonalization
public import QIT.Util.Matrix.KroneckerNorm
public import QIT.Util.Matrix.MarginalOrder
public import QIT.Util.Matrix.SpectralSupport
public import QIT.Util.Matrix.FilteredMarginal
public import QIT.Util.BlockMatrix
public import QIT.Util.RpowOperatorConvex
public import QIT.Util.Order.EReal
public import QIT.Util.TensorPower
public import QIT.Util.Wires
public import QIT.Util.CMatrixCLM
public import QIT.Util.NewtonBinomial
public import QIT.Util.CommutingBinomial
public import QIT.Util.BinomialTail

/-!
# QIT utilities

Quantum-free helper lemmas and notation support used by QIT core modules.
-/

@[expose] public section
