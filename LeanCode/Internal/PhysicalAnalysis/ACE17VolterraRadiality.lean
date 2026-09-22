import ACE15ClosedCartesianAlgebra

noncomputable section
set_option maxHeartbeats 1200000
open Set Filter MeasureTheory
open scoped Topology ContDiff BigOperators
namespace Grad.ActualCenterVolterra
open Grad.ClosedJets Grad.CartesianState Grad.Constraints Grad.NonlinearProduct
open Grad.NonlinearRadial Grad.NonlinearRange Grad.NonlinearQuotientBounds
open Grad.NonlinearDivision (IsRotationInvariant)
open Grad.PhysicalFamily

theorem radial_orthogonal_value {dimension : ℕ} (field : ClosedJet dimension) (radial : IsRotationInvariant field)
    (angle : ℝ) (point : ClosedDisk) :
    field.value (Grad.GaugeCoefficients.Radial.rotatedPoint angle point) = field.value point := by
  convert radial angle point using 1
  congr 1
  apply Subtype.ext
  exact (physicalRotation_eq_orthogonal angle point.val).symm

theorem radial_angularMean {dimension : ℕ} (field : ClosedJet dimension) (radial : IsRotationInvariant field) :
    angularClosedJet 0 field = field := by
  apply closedJet_eq_of_value_eq
  apply ContinuousMap.ext
  intro point
  rw [angularClosedJet_value]
  simp_rw [angularCharacter_zero_mode, one_smul, radial_orthogonal_value field radial]
  rw [intervalIntegral.integral_const, sub_zero, smul_smul, inv_mul_cancel₀ (by positivity : (2 * Real.pi) ≠ 0), one_smul]

theorem radial_rotation_zero {dimension : ℕ} (field : ClosedJet dimension) (radial : IsRotationInvariant field) :
    rotationJet field = 0 := by
  have identity := pureMode_rotation 0 field (radial_angularMean field radial)
  simpa only [Int.cast_zero, mul_zero, zero_smul] using identity

theorem dilation_rotation (scale : ℝ) (nonnegative : 0 ≤ scale) (bounded : scale ≤ 1)
    (angle : ℝ) (point : ClosedDisk) :
    dilationPoint scale nonnegative bounded (Grad.NonlinearDivision.rotatedPoint angle point) =
      Grad.NonlinearDivision.rotatedPoint angle (dilationPoint scale nonnegative bounded point) := by
  apply Subtype.ext
  change scale • planeRotationAction angle point.val = planeRotationAction angle (scale • point.val)
  simp only [physicalRotation_eq_orthogonal]
  exact (map_smul (Grad.GaugeCoefficients.Radial.planeRotationEquiv angle) scale point.val).symm

theorem powerDilation_radial {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension)
    (radial : IsRotationInvariant field) : IsRotationInvariant (powerDilationJet power field) := by
  intro angle point
  rw [powerDilationJet_value, powerDilationJet_value]
  apply setIntegral_congr_fun measurableSet_Icc
  intro scale inside
  dsimp only
  apply congrArg (fun value => scale ^ power • value)
  change smoothClosedExtension field (dilationPoint scale inside.1 inside.2
      (Grad.NonlinearDivision.rotatedPoint angle point)).val =
    smoothClosedExtension field (dilationPoint scale inside.1 inside.2 point).val
  rw [smoothClosedExtension_value, smoothClosedExtension_value, dilation_rotation]
  exact radial angle _

theorem radiusPower_radial {dimension : ℕ} (power : ℕ) (field : ClosedJet dimension)
    (radial : IsRotationInvariant field) : IsRotationInvariant (radiusPowerJet power field) := by
  intro angle point
  rw [radiusPowerJet_value, radiusPowerJet_value, radial angle point, radiusSquare_eq, radiusSquare_eq]
  change (‖planeRotationAction angle point.val‖ ^ 2) ^ power • field.value point = _
  rw [physicalRotation_norm]

theorem volterraJet_radial {dimension : ℕ} (field : ClosedJet dimension)
    (radial : IsRotationInvariant field) : IsRotationInvariant (volterraJet field) :=
  radiusPower_radial 1 _ (powerDilation_radial 1 _ (powerDilation_radial 3 field radial))

theorem volterraPower_radial {dimension : ℕ} (count : ℕ) (field : ClosedJet dimension)
    (radial : IsRotationInvariant field) : IsRotationInvariant (volterraPower count field) := by
  induction count with
  | zero => exact radial
  | succ count previous => exact volterraJet_radial _ previous

theorem volterraResolvent_radial {dimension : ℕ} (parameter : ℝ) (field : ClosedJet dimension)
    (radial : IsRotationInvariant field) : IsRotationInvariant (volterraResolventJet parameter field) := by
  intro angle point
  rw [volterraResolventJet_value, volterraResolventJet_value]
  apply tsum_congr
  intro count
  rw [volterraPower_radial (count + 1) field radial angle point]

theorem radial_neg {dimension : ℕ} (field : ClosedJet dimension)
    (radial : IsRotationInvariant field) : IsRotationInvariant (-field) := by
  intro angle point
  simp only [closedJet_value_neg, ContinuousMap.neg_apply, radial angle point]

end Grad.ActualCenterVolterra
