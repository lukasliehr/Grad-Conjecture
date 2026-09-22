import ANT1CartesianDivCurl
import ANP3SignedDerivativeCovariance

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1600000
namespace Grad.CartesianScalarElimination
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.Constraints.Gauges
open Grad.GaugeCoefficients.Physical.Compensated Grad.GaugeCoefficients.Physical.GaugeTransfer
open Grad.GaugeCoefficients.Physical.RadialLedger Grad.GaugeCoefficients.Physical.Ledger
open Grad.NonlinearRange Grad.NonlinearDivision Grad.ActualMeanInverse Grad.CircularHighWeak
open Grad.ActualCenterVolterra Grad.RawCircularSectors Grad.ActualAngularInverse Grad.CircularHighRegularity

/-- The genuine Euler derivative from its two signed Cartesian derivatives. -/
theorem eulerJet_signed {dimension : ℕ} (field : ClosedJet dimension) :
    eulerJet field = (1 / 2 : ℂ) •
      (coordinateMultiplyJet 1 (centerDifferential 1 field) +
        coordinateMultiplyJet (-1) (centerDifferential (-1) field)) := by
  have positive := centerDifferential_euler 1 (Or.inl rfl) field
  have negative := centerDifferential_euler (-1) (Or.inr rfl) field
  norm_num only [Int.cast_one, Int.cast_neg] at positive negative
  rw [positive, negative]
  module

theorem angularClosedJet_euler {dimension : ℕ} (mode : ℤ) (field : ClosedJet dimension) :
    angularClosedJet mode (eulerJet field) = eulerJet (angularClosedJet mode field) := by
  have negative := centerDifferential_angular (-1) (Or.inr rfl) mode field
  simp only [sub_neg_eq_add] at negative
  rw [eulerJet_signed field, angularClosedJet_smul, angularClosedJet_add,
    angularClosedJet_z, angularClosedJet_zbar,
    ← centerDifferential_angular 1 (Or.inl rfl) mode field, ← negative,
    ← eulerJet_signed]

theorem eulerJet_rotation (field : ClosedJet 1) :
    eulerJet (rotationJet field) = rotationJet (eulerJet field) := by
  apply scalarJet_angular_ext
  intro mode
  rw [angularClosedJet_euler, angular_rotationJet_all, angular_rotationJet_all, angularClosedJet_euler]
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  simp only [eulerJet, Grad.NonlinearQuotientBounds.coordinateJet_value,
    closedJet_value_add, ContinuousMap.add_apply, closedJet_value_smul, ContinuousMap.smul_apply]
  change (point.val 0) • (partialJetLinear 1 0 ((Complex.I * (mode : ℂ)) • angularClosedJet mode field)).value point +
    (point.val 1) • (partialJetLinear 1 1 ((Complex.I * (mode : ℂ)) • angularClosedJet mode field)).value point = _
  rw [map_smul, map_smul]
  simp only [closedJet_value_smul, ContinuousMap.smul_apply, partialJetLinear_apply]
  rw [smul_add, smul_comm (point.val 0), smul_comm (point.val 1)]
  rfl

theorem laplacianJet_rotation (field : ClosedJet 1) :
    laplacianJet (rotationJet field) = rotationJet (laplacianJet field) := by
  apply scalarJet_angular_ext
  intro mode
  rw [← laplacianJet_angular, angular_rotationJet_all, angular_rotationJet_all, ← laplacianJet_angular]
  exact map_smul laplacianJetLinear (Complex.I * (mode : ℂ)) (angularClosedJet mode field)

/-- The literal accepted gradient has zero curl, by equality of its two
mixed Cartesian derivative jets. -/
theorem planarCurlJet_gradient (field : ClosedJet 1) : planarCurlJet (gradientJet field) = 0 := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  have coordinateZero : coordinate = 0 := Subsingleton.elim _ _
  subst coordinate
  change (planarCurlJet (gradientJet field)).value point 0 = 0
  rw [planarCurlJet_value, partialJet_gradient, partialJet_gradient, partialJets_commute 0 1]
  simp [closedJet_value_add, valueMapJet_value, matrixUnit_apply, operatorBasis]

theorem vectorDivJet_gradient (field : ClosedJet 1) : vectorDivJet (gradientJet field) = laplacianJet field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  apply PiLp.ext
  intro coordinate
  have coordinateZero : coordinate = 0 := Subsingleton.elim _ _
  subst coordinate
  change (vectorDivJet (gradientJet field)).value point 0 = (laplacianJet field).value point 0
  rw [vectorDivJet_value]
  rw [partialJet_gradient, partialJet_gradient]
  simp [laplacianJet, closedJet_value_add, valueMapJet_value, matrixUnit_apply, operatorBasis,
    partialJet, Grad.NonlinearQuotientBounds.partialJet]

end Grad.CartesianScalarElimination
