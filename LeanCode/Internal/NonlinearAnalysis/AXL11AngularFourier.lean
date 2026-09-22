import AXL10QuadraticMean

noncomputable section

open MeasureTheory
open scoped Interval

namespace Grad.ChartAxisLift

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.AxisSplit
open Grad.NonlinearQuotientBounds Grad.NonlinearRange Grad.GaugeCoefficients.Radial

theorem coreValue_angularCore {parameters : PhaseParameters} {dimension : ℕ}
    (mode : ℤ) (field : ACore parameters dimension) (point : ClosedDisk) (cellAngle : ℝ) :
    coreValue (angularCore parameters mode field) point cellAngle =
      (2 * Real.pi)⁻¹ • ∫ angle in (0 : ℝ)..2 * Real.pi,
        angularCharacter mode angle • coreValue field (rotatedPoint angle point) cellAngle := by
  let integrand : ℤ → ℝ → ComplexEuclidean dimension := fun cell angle =>
    axialPhase cell cellAngle • (angularCharacter mode angle • (field.val cell).value (rotatedPoint angle point))
  have law : HasSum (fun cell => ∫ angle in (0 : ℝ)..2 * Real.pi, integrand cell angle)
      (∫ angle in (0 : ℝ)..2 * Real.pi,
        angularCharacter mode angle • coreValue field (rotatedPoint angle point) cellAngle) := by
    apply intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun cell _ => ‖(field.val cell).value‖)
    · intro cell
      exact ((angularValueIntegrand_continuous mode (field.val cell) point).const_smul
        (axialPhase cell cellAngle)).aestronglyMeasurable
    · intro cell
      filter_upwards with angle _
      simp only [integrand, norm_smul, norm_axialPhase, angularCharacter_norm, one_mul]
      exact ContinuousMap.norm_coe_le_norm _ _
    · filter_upwards with angle _
      exact Grad.Cor18.cell_sup_norm_summable field
    · exact intervalIntegrable_const
    · filter_upwards with angle _
      have sum := (coreValue_summable field (rotatedPoint angle point) cellAngle).hasSum.const_smul
        (angularCharacter mode angle)
      have commute : (fun cell => angularCharacter mode angle •
          (axialPhase cell cellAngle • (field.val cell).value (rotatedPoint angle point))) =
          (fun cell => integrand cell angle) := by
        funext cell
        exact smul_comm _ _ _
      rw [commute] at sum
      exact sum
  have normalized := law.const_smul ((2 * Real.pi)⁻¹ : ℝ)
  have terms (cell : ℤ) :
      (2 * Real.pi)⁻¹ • (∫ angle in (0 : ℝ)..2 * Real.pi, integrand cell angle) =
      axialPhase cell cellAngle • ((angularCore parameters mode field).val cell).value point := by
    change (2 * Real.pi)⁻¹ • (∫ angle in (0 : ℝ)..2 * Real.pi, integrand cell angle) =
      axialPhase cell cellAngle • (angularClosedJet mode (field.val cell)).value point
    rw [angularClosedJet_value]
    dsimp only [integrand]
    rw [intervalIntegral.integral_smul, smul_comm]
  simp only [terms] at normalized
  exact normalized.tsum_eq

theorem coreValue_angularCore_jet {parameters : PhaseParameters} {dimension : ℕ}
    (mode : ℤ) (field : ACore parameters dimension) (cellAngle : ℝ) (jet : ClosedJet dimension)
    (physical : ∀ point, coreValue field point cellAngle = jet.value point) (point : ClosedDisk) :
    coreValue (angularCore parameters mode field) point cellAngle = (angularClosedJet mode jet).value point := by
  rw [coreValue_angularCore, angularClosedJet_value]
  simp only [physical]

/-- A literal physical quadratic form of trace zero has zero angular mean,
with the Fourier/Bochner exchange justified on the original smooth core. -/
theorem angularCore_of_physical_quadratic {parameters : PhaseParameters}
    (field : ACore parameters 1) (operators : ℝ → ComplexEuclidean 2 →L[ℂ] ComplexEuclidean 2)
    (physical : ∀ point angle, coreValue field point angle = (quadraticMatrixJet (operators angle)).value point)
    (trace : ∀ angle, Gauges.operatorTrace (operators angle) = 0) : angularCore parameters 0 field = 0 := by
  apply coreValue_ext
  intro point angle
  rw [coreValue_angularCore_jet 0 field angle (quadraticMatrixJet (operators angle))
    (fun point => physical point angle), angular_quadraticMatrix_zero _ (trace angle)]
  simp [coreValue]

end Grad.ChartAxisLift
