import AKU17SameWidthAxisAction

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace Grad.FinitePhysicalJetLift
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.GaugeCoefficients.Physical.Allocation Grad.GaugeCoefficients.Algebra
open Grad.NonlinearDivision Grad.PhaseAlgebra Grad.GaugeCoefficients.Physical.Ledger

/-- Axis-core coefficients have an absolutely convergent literal Fourier
series, obtained from their own degree-two Hilbert row. -/
theorem axisData_value_norm_summable {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) : Summable (fun cell => ‖data.val cell‖) := by
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun cell => ?_) (inverseSquareFrequency_summable.mul_right ‖Grad.AxisCore.axisEta parameters dimension 2 data‖)
  rw [inverseSquareFrequency,inv_mul_eq_div]
  apply (le_div_iff₀ (pow_pos (cellFrequency_pos cell) 2)).mpr
  have raw : ‖data.val cell‖ * cellFrequency cell ^ 2 ≤ axisDataNormSequence 2 data cell := by
    rw [axisDataNormSequence_apply,Grad.AxisCore.axisWeight]
    have exponential := Real.one_le_exp (mul_nonneg parameters.sigma0_pos.le (cellFrequency_pos cell).le)
    nlinarith [mul_nonneg (pow_nonneg (cellFrequency_pos cell).le 2) (norm_nonneg (data.val cell))]
  apply raw.trans
  change ‖Grad.AxisCore.axisEta parameters dimension 2 data cell‖ ≤ _
  exact component_norm_le _ _

def axisPhysicalValue {parameters : PhaseParameters} {dimension : ℕ}
    (data : Grad.AxisCore.AxisSmoothCore parameters dimension) (angle : ℝ) : ComplexEuclidean dimension :=
  ∑' cell, fourierPhase cell angle • data.val cell

/-- The original smooth axis action uses the exact same physical matrix at
all Fourier modes. It is not a new pointwise inverse chosen at each angle. -/
theorem axisFamilyAction_physical {parameters : PhaseParameters} {input output : ℕ}
    (family : CoefficientFamily 1 parameters.sigma0 parameters.gamma 1 input output)
    (coherent : FamilyCoherent family) (data : Grad.AxisCore.AxisSmoothCore parameters input) (angle : ℝ) :
    axisPhysicalValue (axisFamilyAction family coherent data) angle =
      coefficientPhysicalValue (family 0) angle closedOrigin (axisPhysicalValue data angle) := by
  change (∑' cell, fourierPhase cell angle • ∑' shift,
    axisFamilyOperator family shift (data.val (cell-shift))) = _
  exact Grad.Constraints.Gauges.operatorVectorConvolution_fourier (axisFamilyOperator family) data.val
    (Grad.Constraints.Gauges.coefficientNorm_summable parameters _
      (axisFamilyOperator_envelope_summable family coherent 0))
    (axisData_value_norm_summable data) angle

end Grad.FinitePhysicalJetLift
