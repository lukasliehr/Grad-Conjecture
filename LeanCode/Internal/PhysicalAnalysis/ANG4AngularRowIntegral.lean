import ANG3RotatedGradient

noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 200000
open Set MeasureTheory
open scoped BigOperators
namespace Grad.CircularHighWeak
open Grad.ClosedJets Grad.CartesianState Grad.Constraints
open Grad.GaugeCoefficients.Radial Grad.GaugeCoefficients.Envelope Grad.GaugeCoefficients.Algebra
open Grad.GaugeCoefficients.Physical.RadialLedger

def unitAngularRow (mode : ℤ) (field : ClosedJet 1) (angle : ℝ) : APRow 1 1 :=
  angularCharacter mode angle • apRowLinear 1 0 0 1 0 (orthogonalJet (planeRotationEquiv angle) field)

theorem unitAngularRow_coordinate (mode : ℤ) (field : ClosedJet 1) (angle : ℝ) (index : DerivativeIndex 1) :
    unitAngularRow mode field angle index =
      closedContinuousToDiskL2 (angularDerivativeFamily mode field
        (cartesianMultiIndexWord (derivativeMultiIndex index)) angle) := by
  change angularCharacter mode angle • apRowLinear 1 0 0 1 0 (orthogonalJet (planeRotationEquiv angle) field) index = _
  rw [apRowLinear_apply, unweightedJet]
  simp only [show scaledCellWeight 1 1 0 = 1 by norm_num [scaledCellWeight], Complex.ofReal_one, one_pow, one_smul]
  change angularCharacter mode angle • closedContinuousToDiskL2 (closedDerivative
    (orthogonalJet (planeRotationEquiv angle) field) (cartesianOrder (derivativeMultiIndex index))
    (cartesianMultiIndexWord (derivativeMultiIndex index))) = _
  rw [orthogonalJet_derivative]
  exact (closedContinuousToDiskL2_smul _ _).symm

theorem unitAngularRow_continuous (mode : ℤ) (field : ClosedJet 1) : Continuous (unitAngularRow mode field) := by
  have each (index : DerivativeIndex 1) : Continuous (fun angle => unitAngularRow mode field angle index) := by
    simp_rw [unitAngularRow_coordinate]
    exact (closedValueL2Continuous 1).continuous.comp
      (angularDerivativeFamily_continuous mode field (cartesianMultiIndexWord (derivativeMultiIndex index)))
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi each)

theorem unitAngularRow_norm (mode : ℤ) (field : ClosedJet 1) (angle : ℝ) :
    ‖unitAngularRow mode field angle‖ = ‖apRowLinear (grade := 1) 1 0 0 1 0 field‖ := by
  rw [unitAngularRow, norm_smul, angularCharacter_norm, one_mul, rotatedJet_unitRow_norm]

/-- The completed H1 row is the actual Bochner angular average of the
rotated Cartesian rows, retaining their coupled gradient coordinates. -/
theorem angularRow_integral (mode : ℤ) (field : ClosedJet 1) :
    apRowLinear (grade := 1) 1 0 0 1 0 (angularClosedJet mode field) =
      ((2 * Real.pi)⁻¹ : ℝ) • ∫ angle in Icc (0 : ℝ) (2 * Real.pi), unitAngularRow mode field angle := by
  apply PiLp.ext
  intro index
  rw [apRowLinear_apply, unweightedJet]
  simp only [show scaledCellWeight 1 1 0 = 1 by norm_num [scaledCellWeight], Complex.ofReal_one, one_pow, one_smul]
  change closedContinuousToDiskL2 (closedDerivative (angularClosedJet mode field) (cartesianOrder (derivativeMultiIndex index))
    (cartesianMultiIndexWord (derivativeMultiIndex index))) = _
  rw [angularClosedJet_derivative_continuousMap, closedValueL2_real_smul,
    closedValueL2_integral (angularDerivativeFamily_continuous mode field
      (cartesianMultiIndexWord (derivativeMultiIndex index))).continuousOn.integrableOn_Icc]
  have integrableRow : IntegrableOn (unitAngularRow mode field) (Icc (0 : ℝ) (2 * Real.pi)) :=
    (unitAngularRow_continuous mode field).continuousOn.integrableOn_Icc
  have integralCoordinate := ((PiLp.proj (𝕜 := ℂ) 2 (fun _ : DerivativeIndex 1 => DiskL2 1) index).integral_comp_comm
    integrableRow).symm
  change _ = (2 * Real.pi)⁻¹ • (∫ angle in Icc (0 : ℝ) (2 * Real.pi), unitAngularRow mode field angle) index
  change (∫ angle in Icc (0 : ℝ) (2 * Real.pi), unitAngularRow mode field angle) index =
    ∫ angle in Icc (0 : ℝ) (2 * Real.pi), unitAngularRow mode field angle index at integralCoordinate
  rw [integralCoordinate]
  congr 1
  apply setIntegral_congr_fun measurableSet_Icc
  intro angle _
  exact (unitAngularRow_coordinate mode field angle index).symm

end Grad.CircularHighWeak
