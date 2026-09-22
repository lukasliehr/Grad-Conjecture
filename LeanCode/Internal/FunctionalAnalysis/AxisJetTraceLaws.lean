import AxisJetInsertion

noncomputable section

open scoped BigOperators ContDiff

namespace Grad.AxisJet

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearQuotientBounds Grad.AxisSplit

variable {parameters : PhaseParameters}

/-! ### M31: the literal trace laws `J0 E0 = I`, `J_i E0 = 0`, `J0 E_j = 0`,
`J_i E_j = δ_{ij} I` -/

theorem traceZero_insertZero {dimension : ℕ}
    (family : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    traceZero (insertZero family) = family := by
  apply Subtype.ext
  funext cell
  show originValue ((insertZero family).val cell) = family.val cell
  rw [insertZero_val, profileJetZero_originValue]

theorem traceFirst_insertZero {dimension : ℕ} (direction : Fin 2)
    (family : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    traceFirst direction (insertZero family) = 0 := by
  apply Subtype.ext
  funext cell
  show originPartial direction ((insertZero family).val cell) = _
  rw [insertZero_val, profileJetZero_originPartial]
  rfl

theorem traceZero_insertOne {dimension : ℕ} (coordinate : Fin 2)
    (family : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    traceZero (insertOne coordinate family) = 0 := by
  apply Subtype.ext
  funext cell
  show originValue ((insertOne coordinate family).val cell) = _
  rw [insertOne_val, profileJetOne_originValue]
  rfl

theorem traceFirst_insertOne {dimension : ℕ} (direction coordinate : Fin 2)
    (family : Grad.AxisCore.AxisSmoothCore parameters dimension) :
    traceFirst direction (insertOne coordinate family) =
      if direction = coordinate then family else 0 := by
  apply Subtype.ext
  funext cell
  show originPartial direction ((insertOne coordinate family).val cell) = _
  rw [insertOne_val, profileJetOne_originPartial]
  by_cases equal : direction = coordinate
  · rw [if_pos equal, if_pos equal]
  · rw [if_neg equal, if_neg equal]
    rfl

/-! ### M29: the literal scaled-kernel factorization of the phased profiles -/

/-- M29's fixed kernel `ψ0(t) = e^{-γ(√(1+|t|²)-1)} φ(t)`. -/
def scaledKernel (parameters : PhaseParameters) : SpatialPlane → ℝ :=
  fun target =>
    Real.exp (-parameters.gamma * (Real.sqrt (1 + ‖target‖ ^ 2) - 1)) * jetBump target

/-- M29's coordinate kernel `ψ_i(t) = t_i ψ0(t)`. -/
def scaledKernelOne (parameters : PhaseParameters) (coordinate : Fin 2) :
    SpatialPlane → ℝ :=
  fun target => coordinateLinear coordinate target * scaledKernel parameters target

/-- The scalar core of M29: the phase weight times the scaled bump is the
frequency exponential times the dilated kernel. -/
theorem phase_kernel_identity (parameters : PhaseParameters) (cell : ℤ)
    (point : SpatialPlane) :
    cartesianWeight parameters cell point * jetBump (cellFrequency cell • point) =
      Real.exp (parameters.sigma0 * cellFrequency cell) *
        scaledKernel parameters (cellFrequency cell • point) := by
  obtain ⟨-, phaseFormula, weightFormula, -, -⟩ :=
    Grad.AnalyticWeights.Calculus.Consumer.actualFormulas parameters.sigma0
      parameters.gamma 1 cell point
  have radicandForm : Grad.AnalyticWeights.Calculus.radicand 1 cell point =
      1 + ‖cellFrequency cell • point‖ ^ 2 := by
    unfold Grad.AnalyticWeights.Calculus.radicand
    rw [norm_smul, Real.norm_of_nonneg (cellFrequency_pos cell).le, mul_pow]
    have frequencyEq : cellFrequency cell = Grad.CellWeights.cellWeight cell := rfl
    rw [← frequencyEq]
    ring
  unfold scaledKernel
  rw [show cartesianWeight parameters cell point =
      Real.exp (Grad.AnalyticWeights.Calculus.physicalPhase parameters.sigma0
        parameters.gamma 1 cell point) from weightFormula,
    phaseFormula, radicandForm, sub_eq_add_neg, Real.exp_add]
  have frequencyEq : Grad.CellWeights.cellWeight cell = cellFrequency cell := rfl
  rw [frequencyEq]
  ring_nf

/-- M29 for the value profile: `e^{Φ_n} (E0 a)_n = e^{σ0 λ_n} a_n ψ0(λ_n ·)`,
stated as the exact value of the phase-weighted profile jet. -/
theorem phased_profileZero_value {dimension : ℕ} (cell : ℤ)
    (vector : ComplexEuclidean dimension) (point : ClosedDisk) :
    (phaseWeightedJet parameters cell (profileJetZero cell vector)).value point =
      (Real.exp (parameters.sigma0 * cellFrequency cell) *
        scaledKernel parameters (cellFrequency cell • point.val)) • vector := by
  change cartesianWeight parameters cell point.val •
    (profileScalarZero cell point.val • vector) = _
  rw [← mul_smul]
  rw [show cartesianWeight parameters cell point.val *
      profileScalarZero cell point.val =
    Real.exp (parameters.sigma0 * cellFrequency cell) *
      scaledKernel parameters (cellFrequency cell • point.val) from
    phase_kernel_identity parameters cell point.val]

/-- M29 for the coordinate profiles:
`e^{Φ_n} (E_i a)_n = e^{σ0 λ_n} λ_n⁻¹ a_n ψ_i(λ_n ·)`, stated as the exact
value of the phase-weighted profile jet, with the literal `λ_n⁻¹`. -/
theorem phased_profileOne_value {dimension : ℕ} (coordinate : Fin 2) (cell : ℤ)
    (vector : ComplexEuclidean dimension) (point : ClosedDisk) :
    (phaseWeightedJet parameters cell
        (profileJetOne coordinate cell vector)).value point =
      (Real.exp (parameters.sigma0 * cellFrequency cell) * (cellFrequency cell)⁻¹ *
        scaledKernelOne parameters coordinate
          (cellFrequency cell • point.val)) • vector := by
  change cartesianWeight parameters cell point.val •
    (profileScalarOne coordinate cell point.val • vector) = _
  rw [← mul_smul]
  have coordinateScale :
      coordinateLinear coordinate (cellFrequency cell • point.val) =
        cellFrequency cell * coordinateLinear coordinate point.val := by
    rw [(coordinateLinear coordinate).map_smul]
    rfl
  have scalarIdentity : cartesianWeight parameters cell point.val *
      profileScalarOne coordinate cell point.val =
      Real.exp (parameters.sigma0 * cellFrequency cell) * (cellFrequency cell)⁻¹ *
        scaledKernelOne parameters coordinate (cellFrequency cell • point.val) := by
    unfold scaledKernelOne
    rw [coordinateScale]
    have kernelSide := phase_kernel_identity parameters cell point.val
    show cartesianWeight parameters cell point.val *
        (coordinateLinear coordinate point.val *
          jetBump (cellFrequency cell • point.val)) = _
    rw [show Real.exp (parameters.sigma0 * cellFrequency cell) *
        (cellFrequency cell)⁻¹ *
        (cellFrequency cell * coordinateLinear coordinate point.val *
          scaledKernel parameters (cellFrequency cell • point.val)) =
      ((cellFrequency cell)⁻¹ * cellFrequency cell) *
        (coordinateLinear coordinate point.val *
          (Real.exp (parameters.sigma0 * cellFrequency cell) *
            scaledKernel parameters (cellFrequency cell • point.val))) from by ring,
      inv_mul_cancel₀ (cellFrequency_pos cell).ne', one_mul, ← kernelSide]
    ring
  rw [scalarIdentity]

end Grad.AxisJet
