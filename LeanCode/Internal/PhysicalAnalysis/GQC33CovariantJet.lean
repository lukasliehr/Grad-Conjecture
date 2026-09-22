import GQC30APSmoothFaithfulness

noncomputable section

set_option maxHeartbeats 1600000

open Set MeasureTheory
open scoped Topology Interval

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Radial

def gradientJet (field : ClosedJet 1) : ClosedJet 2 :=
  valueMapJet (matrixUnit 0 0) (partialJet 0 field) +
    valueMapJet (matrixUnit 1 0) (partialJet 1 field)

theorem gradientJet_value (field : ClosedJet 1) (point : ClosedDisk) :
    (gradientJet field).value point = WithLp.toLp 2 ![
      (partialJet 0 field).value point 0, (partialJet 1 field).value point 0] := by
  apply PiLp.ext
  intro coordinate
  simp only [gradientJet, closedJet_value_add, ContinuousMap.add_apply, valueMapJet_value,
    matrixUnit_apply, PiLp.add_apply, PiLp.smul_apply]
  fin_cases coordinate <;> simp [operatorBasis]

def covariantJet (frequency : ℂ) (field : ClosedJet 1) : ClosedJet 3 :=
  valueMapJet planarInclusionMap (gradientJet field) +
    frequency • valueMapJet toroidalInclusionMap field

theorem covariantJet_value (frequency : ℂ) (field : ClosedJet 1) (point : ClosedDisk) :
    (covariantJet frequency field).value point = WithLp.toLp 2 ![
      (partialJet 0 field).value point 0, (partialJet 1 field).value point 0,
      frequency * field.value point 0] := by
  rw [covariantJet, closedJet_value_add, ContinuousMap.add_apply, closedJet_value_smul,
    ContinuousMap.smul_apply, valueMapJet_value, valueMapJet_value, gradientJet_value]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [planarInclusionMap, toroidalInclusionMap]

theorem covariantJet_tangent (frequency : ℂ) (field : ClosedJet 1) (point : ClosedDisk) :
    storedTangentDot point ((covariantJet frequency field).value point) =
      (Grad.NonlinearRange.rotationJet field).value point 0 := by
  rw [covariantJet_value]
  simp only [storedTangentDot, Grad.NonlinearRange.rotationJet, sub_eq_add_neg,
    closedJet_value_add, closedJet_value_neg, ContinuousMap.add_apply,
    ContinuousMap.neg_apply, Grad.NonlinearQuotientBounds.coordinateJet_value,
    PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  change -(point.val 1 : ℂ) * (partialJet 0 field).value point 0 +
    (point.val 0 : ℂ) * (partialJet 1 field).value point 0 =
    (point.val 0) • (partialJet 1 field).value point 0 +
      -((point.val 1) • (partialJet 0 field).value point 0)
  simp only [Complex.real_smul]
  ring

/-- The actual circular average kills the genuine Cartesian rotation
derivative, by the fundamental theorem over the original full period. -/
theorem angularClosedJet_rotation_zero {dimension : ℕ} (field : ClosedJet dimension) :
    angularClosedJet 0 (Grad.NonlinearRange.rotationJet field) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  change (angularClosedJet 0 (Grad.NonlinearRange.rotationJet field)).value point = 0
  rw [angularClosedJet_value]
  simp only [angularCharacter_zero_mode, one_smul]
  have continuous : Continuous (fun angle =>
      (Grad.NonlinearRange.rotationJet field).value (rotatedPoint angle point)) := by
    simpa only [angularCharacter_zero_mode, one_smul] using
      angularValueIntegrand_continuous 0 (Grad.NonlinearRange.rotationJet field) point
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun angle _ => closedOrbit_hasDerivAt field point angle)
    (continuous.intervalIntegrable 0 (2 * Real.pi))]
  have periodic : rotatedPoint (2 * Real.pi) point = rotatedPoint 0 point := by
    apply Subtype.ext
    simpa only [zero_add, rotatedPoint, physicalRotation_eq_orthogonal, planeRotationEquiv_apply] using
      physicalRotation_periodic point.val 0
  rw [periodic, sub_self, smul_zero]

theorem closedAngularMean_jet {dimension : ℕ} (field : ClosedJet dimension) (point : ClosedDisk) :
    closedAngularMean field.value point = (angularClosedJet 0 field).value point := by
  rw [closedAngularMean, normalizedAngularIntegral (fun angle => field.value (rotatedPoint angle point)),
    angularClosedJet_value]
  simp only [angularCharacter_zero_mode, one_smul]
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]

end Grad.GaugeCoefficients.Physical.Compensated
