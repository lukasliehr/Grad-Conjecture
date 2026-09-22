import GQF11SmoothComparison

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Radial
open Grad.NonlinearRange Grad.NonlinearQuotientBounds Grad.AxisSplit

theorem partialJet_coordinate_value {dimension : ℕ} (direction coordinate : Fin 2)
    (field : ClosedJet dimension) (point : ClosedDisk) :
    (partialJet direction (coordinateJet coordinate field)).value point =
      spatialBasis direction coordinate • field.value point +
        point.val coordinate • (partialJet direction field).value point := by
  have product := smoothScalar_partial_value (coordinateLinear coordinate)
    (coordinateLinear coordinate).contDiff field direction point
  have derivative : spatialPartial direction (coordinateLinear coordinate) point.val =
      spatialBasis direction coordinate := by
    unfold spatialPartial
    rw [(coordinateLinear coordinate).fderiv]
    rfl
  rw [derivative] at product
  exact product

theorem partialCoefficient_coordinate_value {dimension : ℕ} (direction coordinate : Fin 2)
    (field : ClosedJet dimension) (point : ClosedDisk) :
    partialCoefficient direction (coordinateJet coordinate field) point =
      spatialBasis direction coordinate • field.value point +
        point.val coordinate • partialCoefficient direction field point :=
  partialJet_coordinate_value direction coordinate field point

theorem radialRowJet_representation (field : ClosedJet 3) :
    apProductJet radialRowJet field =
      valueMapJet (matrixUnit 0 0) (coordinateJet 0 field) +
        valueMapJet (matrixUnit 0 1) (coordinateJet 1 field) := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change (apProductJet radialRowJet field).value point 0 =
    (valueMapJet (matrixUnit 0 0) (coordinateJet 0 field) +
      valueMapJet (matrixUnit 0 1) (coordinateJet 1 field)).value point 0
  rw [apProductJet_value, radialRowJet_value]
  simp [closedJet_value_add, valueMapJet_value, coordinateJet_value,
    matrixUnit_apply, operatorBasis, Complex.real_smul]

/-- Actual Cartesian product rule for the radial contraction and R.
Its mean is zero by the literal full-period fundamental theorem. -/
theorem rotationJet_radialRow (field : ClosedJet 3) :
    rotationJet (apProductJet radialRowJet field) =
      apProductJet tangentRowJet field + apProductJet radialRowJet (rotationJet field) := by
  rw [radialRowJet_representation, rotationJet_add, rotationJet_valueMap, rotationJet_valueMap]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate
  change (valueMapJet (matrixUnit 0 0) (rotationJet (coordinateJet 0 field)) +
    valueMapJet (matrixUnit 0 1) (rotationJet (coordinateJet 1 field))).value point 0 =
      (apProductJet tangentRowJet field + apProductJet radialRowJet (rotationJet field)).value point 0
  simp only [rotationJet, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, coordinateJet_value,
    valueMapJet_value, apProductJet_value, PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply,
    Complex.real_smul, matrixUnit_apply, operatorBasis]
  simp [partialCoefficient_coordinate_value, radialRowJet_value, tangentRowJet_value,
    storedTangentDot, spatialBasis, Complex.real_smul]
  ring

theorem radialRotation_mean (field : ClosedJet 3) (point : ClosedDisk) :
    closedAngularMean (fun other => storedTangentDot other (field.value other)) point +
      closedAngularMean (fun other =>
        (other.val 0 : ℂ) * (rotationJet field).value other 0 +
          (other.val 1 : ℂ) * (rotationJet field).value other 1) point = 0 := by
  have identity := congrArg (angularClosedJet 0) (rotationJet_radialRow field)
  rw [angularClosedJet_rotation_zero, angularClosedJet_add] at identity
  have value := congrArg (fun jet : ClosedJet 1 => jet.value point 0) identity.symm
  simpa only [closedJet_value_add, ContinuousMap.add_apply, PiLp.add_apply,
    scalarMean_value, apProductJet_value, tangentRowJet_value, radialRowJet_value,
    closedJet_value_zero, ContinuousMap.zero_apply, PiLp.zero_apply] using value

end Grad.GaugeCoefficients.Physical.Compensated
