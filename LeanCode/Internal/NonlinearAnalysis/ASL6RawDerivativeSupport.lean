import ASL5RawLocality

noncomputable section

set_option maxRecDepth 3000
set_option maxHeartbeats 1200000

open Filter
open scoped Topology

namespace Grad.AxisSourceLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearQuotientBounds
open Grad.NonlinearProduct Grad.NonlinearRange Grad.RawForward

variable {parameters : PhaseParameters}

theorem rawReconstruction_rowsDirectional
    (mapping : QuotientState parameters → QuotientRows parameters)
    (base direction : QuotientState parameters) (derivative : QuotientRows parameters)
    (genuine : IsRowsDirectionalDerivative mapping base direction derivative) :
    IsRowsDirectionalDerivative (fun point => rawReconstructionCore parameters (mapping point))
      base direction (rawReconstructionCore parameters derivative) := by
  intro grade
  obtain ⟨constant, _, bound⟩ := rawReconstructionCore_rows_bound (parameters := parameters) grade
  have limit := (genuine grade).const_mul constant
  rw [mul_zero] at limit
  refine squeeze_zero (fun _ => rowsGradeNorm_nonneg _ _) (fun scalar => ?_) limit
  have estimate := bound
    ((scalar : ℂ)⁻¹ • (mapping (base + (scalar : ℂ) • direction) - mapping base) - derivative)
  simpa only [map_sub, map_smul] using estimate

theorem gaugeState_line (base direction : QuotientState parameters)
    (baseGauge : GaugeState parameters base) (directionGauge : GaugeState parameters direction)
    (scalar : ℂ) : GaugeState parameters (base + scalar • direction) := by
  unfold GaugeState at *
  rw [map_add, map_smul, map_add, map_smul, baseGauge, directionGauge, smul_zero, add_zero]

/-- Differentiate the literal raw identity, then use the actual local raw
equations. No locality is asserted for the radial quotient operator. -/
theorem rawQuotientDerivative_zero_outside (cellLength : ℝ) (radius : ℝ)
    (base direction : QuotientState parameters)
    (baseGauge : GaugeState parameters base) (directionGauge : GaugeState parameters direction)
    (scalarZero : stateScalar direction = 0)
    (fieldZero : FirstOutsideEqual radius (stateField direction) 0)
    (potentialZero : FirstOutsideEqual radius (statePotential direction) 0)
    (row : Fin 4) (cell : ℤ) (point : ClosedDisk) (outside : radius ≤ ‖point.val‖) :
    ((rawReconstructionCore parameters
      (quotientRowsDerivative parameters cellLength 1 base (fun _ => direction)) row).val cell).value point = 0 := by
  have quotientGenuine := quotientRowsDerivative_genuine cellLength 0 base (fun _ => direction)
  simp only [quotientRowsDerivative_zeroth] at quotientGenuine
  have rawGenuine := rawReconstruction_rowsDirectional
    (quotientPolynomialRows parameters cellLength) base direction
    (quotientRowsDerivative parameters cellLength 1 base (fun _ => direction)) quotientGenuine
  have evaluated := rowsDirectional_value (E := QuotientState parameters)
    (fun state => rawReconstructionCore parameters (quotientPolynomialRows parameters cellLength state))
    base direction
    (rawReconstructionCore parameters (quotientRowsDerivative parameters cellLength 1 base (fun _ => direction)))
    rawGenuine row cell point
  have constantCurve : (fun scalar : ℝ => rowCoefficientValue row cell point
      (rawReconstructionCore parameters
        (quotientPolynomialRows parameters cellLength (base + (scalar : ℂ) • direction)))) =
      fun _ : ℝ => rowCoefficientValue row cell point (originalRawRowsCore parameters cellLength base) := by
    funext scalar
    rw [rawReconstruction_polynomial cellLength _ (gaugeState_line base direction baseGauge directionGauge _)]
    exact originalRawRowsCore_cap_line cellLength base direction scalarZero fieldZero potentialZero
      (scalar : ℂ) row cell point outside
  rw [constantCurve] at evaluated
  exact evaluated.unique (hasDerivAt_const 0 _)

/-- Pointwise support of the actual quotient derivative follows from the four
raw rows and J_Y injectivity at the same nonzero point. -/
theorem quotientDerivative_zero_outside (cellLength : ℝ) (radius : ℝ) (positive : 0 < radius)
    (base direction : QuotientState parameters)
    (baseGauge : GaugeState parameters base) (directionGauge : GaugeState parameters direction)
    (scalarZero : stateScalar direction = 0)
    (fieldZero : FirstOutsideEqual radius (stateField direction) 0)
    (potentialZero : FirstOutsideEqual radius (statePotential direction) 0)
    (row : Fin 4) (cell : ℤ) (point : ClosedDisk) (outside : radius ≤ ‖point.val‖) :
    ((quotientRowsDerivative parameters cellLength 1 base (fun _ => direction) row).val cell).value point = 0 := by
  apply rawReconstruction_pointwise_injective _ cell point
    (norm_ne_zero_iff.mp (ne_of_gt (positive.trans_le outside))) _ row
  intro index
  exact rawQuotientDerivative_zero_outside cellLength radius base direction baseGauge directionGauge
    scalarZero fieldZero potentialZero index cell point outside

end Grad.AxisSourceLift
