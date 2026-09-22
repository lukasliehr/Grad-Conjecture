import GQF17RadialSourceJets

noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000

namespace Grad.GaugeCoefficients.Physical.Compensated

open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Algebra Grad.GaugeCoefficients.Envelope
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.GaugeCoefficients.Physical.GaugeTransfer Grad.GaugeCoefficients.Physical.Frame
open Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.NonlinearDivision

theorem planarCurlJet_value (field : ClosedJet 2) (point : ClosedDisk) :
    (planarCurlJet field).value point 0 =
      (partialJet 0 field).value point 1 - (partialJet 1 field).value point 0 := by
  change (valueMapJet (matrixUnit 0 1) (partialJet 0 field) -
    valueMapJet (matrixUnit 0 0) (partialJet 1 field)).value point 0 = _
  simp [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg, valueMapJet_value,
    matrixUnit_apply, operatorBasis]

theorem rotationJet_origin_zero {dimension : ℕ} (field : ClosedJet dimension) :
    (rotationJet field).value closedOrigin = 0 := by
  simp [rotationJet, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    coordinateJet_value, closedOrigin]

theorem partialJet_rotation_origin {dimension : ℕ} (field : ClosedJet dimension) (direction : Fin 2) :
    (partialJet direction (rotationJet field)).value closedOrigin =
      spatialBasis direction 0 • (partialJet 1 field).value closedOrigin -
        spatialBasis direction 1 • (partialJet 0 field).value closedOrigin := by
  change (partialJetLinear dimension direction
    (coordinateJet 0 (partialJet 1 field) - coordinateJet 1 (partialJet 0 field))).value closedOrigin = _
  rw [map_sub, partialJetLinear_apply, partialJetLinear_apply]
  simp only [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    ContinuousMap.add_apply, ContinuousMap.neg_apply]
  rw [partialJet_coordinate_value, partialJet_coordinate_value]
  simp [closedOrigin]

def planarDivergenceValue (field : ClosedJet 2) (point : ClosedDisk) : ℂ :=
  (partialJet 0 field).value point 0 + (partialJet 1 field).value point 1

theorem planarCurlJet_rotation_origin (field : ClosedJet 2) :
    (planarCurlJet (rotationJet field)).value closedOrigin 0 = planarDivergenceValue field closedOrigin := by
  rw [planarCurlJet_value, partialJet_rotation_origin, partialJet_rotation_origin]
  simp [spatialBasis, planarDivergenceValue, add_comm]

theorem planarCurlJet_quarter_value (field : ClosedJet 2) (point : ClosedDisk) :
    (planarCurlJet (valueMapJet quarterValueMap field)).value point 0 = planarDivergenceValue field point := by
  rw [planarCurlJet_value, partialJet_valueMap, partialJet_valueMap, valueMapJet_value, valueMapJet_value]
  simp [quarterValueMap, quarterValueLinear, planarDivergenceValue]

theorem planarDivergence_gradient (field : ClosedJet 1) (point : ClosedDisk) :
    planarDivergenceValue (gradientJet field) point =
      (partialJet 0 (partialJet 0 field)).value point 0 +
        (partialJet 1 (partialJet 1 field)).value point 0 := by
  unfold planarDivergenceValue
  rw [partialJet_gradient, partialJet_gradient]
  simp [closedJet_value_add, valueMapJet_value, matrixUnit_apply, operatorBasis]

theorem planarDivergence_planar (field : ClosedJet 3) (point : ClosedDisk) :
    planarDivergenceValue (valueMapJet planarPartMap field) point =
      (partialJet 0 field).value point 0 + (partialJet 1 field).value point 1 := by
  unfold planarDivergenceValue
  rw [partialJet_valueMap, partialJet_valueMap, valueMapJet_value, valueMapJet_value]
  rfl

def closedCircularForce (theta : ClosedJet 1) (remainder : ClosedJet 3) : ClosedJet 2 :=
  (-2 : ℂ) • valueMapJet quarterValueMap (gradientJet theta) -
    (rotationJet (valueMapJet planarPartMap remainder) +
      valueMapJet quarterValueMap (valueMapJet planarPartMap remainder))

theorem closedCircularForce_origin (frequency : ℂ) (theta : ClosedJet 1) (remainder : ClosedJet 3)
    (thetaFlat : ClosedFirstJetZero theta) (flat : ClosedFirstJetZero (covariantJet frequency theta + remainder)) :
    (closedCircularForce theta remainder).value closedOrigin = 0 := by
  have axis := closedCompensated_axis frequency theta remainder thetaFlat flat
  simp only [closedCircularForce, sub_eq_add_neg, closedJet_value_add, closedJet_value_neg,
    closedJet_value_smul, ContinuousMap.add_apply, ContinuousMap.neg_apply, ContinuousMap.smul_apply,
    rotationJet_origin_zero, valueMapJet_value, gradientJet_value, thetaFlat.2 0, thetaFlat.2 1,
    axis.1, PiLp.zero_apply, map_zero, neg_zero, add_zero]
  apply PiLp.ext
  intro coordinate
  fin_cases coordinate <;> simp [quarterValueMap, quarterValueLinear]

/-- The force curl cancels by Dv_c(0)=-D²Theta(0), not by setting Dv_c to zero. -/
theorem closedCircularForce_curl_origin (frequency : ℂ) (theta : ClosedJet 1) (remainder : ClosedJet 3)
    (thetaFlat : ClosedFirstJetZero theta) (flat : ClosedFirstJetZero (covariantJet frequency theta + remainder)) :
    (planarCurlJet (closedCircularForce theta remainder)).value closedOrigin 0 = 0 := by
  have axis := closedCompensated_axis frequency theta remainder thetaFlat flat
  have expand : planarCurlJet (closedCircularForce theta remainder) =
      (-2 : ℂ) • planarCurlJet (valueMapJet quarterValueMap (gradientJet theta)) -
        (planarCurlJet (rotationJet (valueMapJet planarPartMap remainder)) +
          planarCurlJet (valueMapJet quarterValueMap (valueMapJet planarPartMap remainder))) := by
    exact (planarCurlLinear.map_sub _ _).trans
      (congrArg₂ (fun first second : ClosedJet 1 => first - second)
        (planarCurlLinear.map_smul (-2 : ℂ) _) (planarCurlLinear.map_add _ _))
  rw [expand]
  simp only [sub_eq_add_neg, closedJet_value_add, closedJet_value_neg, closedJet_value_smul,
    ContinuousMap.add_apply, ContinuousMap.neg_apply, ContinuousMap.smul_apply,
    PiLp.add_apply, PiLp.neg_apply, PiLp.smul_apply, smul_eq_mul,
    planarCurlJet_quarter_value, planarCurlJet_rotation_origin, planarDivergence_gradient,
    planarDivergence_planar, axis.2.1 0, axis.2.2.1 1]
  ring

end Grad.GaugeCoefficients.Physical.Compensated
